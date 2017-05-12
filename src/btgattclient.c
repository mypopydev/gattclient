/**
 * @file btgattclient.c
 * @brief bluetooth main gatt client
 *
 * the original file is in bluez/tools and the name is btgatt-client.c
 *
 * @author Gilbert Brault
 * @copyright Gilbert Brault 2015
 * the original work comes from bluez v5.39
 * value add: documenting main features
 *
 */

/*
 *  BlueZ - Bluetooth protocol stack for Linux
 *
 *  Copyright (C) 2014  Google Inc.
 *
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <limits.h>
#include <errno.h>

#include <sys/types.h>
#include <sys/wait.h>

#include <sys/un.h>
#include <sys/socket.h>
#include <ctype.h>
#include <unistd.h>

#include "bluetooth.h"
#include "hci.h"
#include "hci_lib.h"
#include "l2cap.h"
#include "uuid.h"

#include "mainloop.h"
#include "util.h"
#include "att.h"
#include "queue.h"
#include "gatt-db.h"
#include "gatt-client.h"

#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/hci_lib.h>
#include <bluetooth/sdp.h>
#include <bluetooth/sdp_lib.h>
#include <bluetooth/rfcomm.h>

#define ATT_CID 4

#define PRLOG(...) \
	printf(__VA_ARGS__); print_prompt();

#define COLOR_OFF	"\x1B[0m"
#define COLOR_RED	"\x1B[0;91m"
#define COLOR_GREEN	"\x1B[0;92m"
#define COLOR_YELLOW	"\x1B[0;93m"
#define COLOR_BLUE	"\x1B[0;94m"
#define COLOR_MAGENTA	"\x1B[0;95m"
#define COLOR_BOLDGRAY	"\x1B[1;30m"
#define COLOR_BOLDWHITE	"\x1B[1;36m"

static bool verbose = false;

/**
 * client structure holds gatt client context
 */
struct client {
	/// socket
	int fd;
	/// pointer to a bt_att structure
	struct bt_att *att;
	/// pointer to a gatt_db structure
	struct gatt_db *db;
	/// pointer to a bt_gatt_client structure
	struct bt_gatt_client *gatt;
	/// session id
	unsigned int reliable_session_id;
};

#define SERVER "/tmp/ud_bluetooth_main"
#define CLIENT "/tmp/ud_bluetooth_client"

#define BUF_SIZE 128
char buf[BUF_SIZE] = {0};


#define NELEMS(array) (sizeof(array) / sizeof(array[0]))

#include <stdarg.h>
#include <time.h>
#include <sys/time.h>
#include <syslog.h>

static void LOG(const char *fmt, ...)
{
	char date[20];
	struct timeval tv;
	va_list args;

	/* print the timestamp */
	gettimeofday(&tv, NULL);
	strftime(date, NELEMS(date), "%Y-%m-%dT%H:%M:%S", localtime(&tv.tv_sec));
	printf("[%s.%03dZ] ", date, (int)tv.tv_usec/1000);

	/* printf like normal */
	va_start(args, fmt);
	vprintf(fmt, args);
	va_end(args);

        /* send the message to syslog */
        va_start(args, fmt);
        vsyslog(LOG_INFO, fmt, args);
        va_end(args);
}

static int sock_send_cmd(int sock, char *server_path, char *cmd, int cmd_len)
{
        struct sockaddr_un svaddr;
        int len = sizeof(struct sockaddr_un);

        memset(&svaddr, 0, sizeof(struct sockaddr_un));
        svaddr.sun_family = AF_UNIX;
        strncpy(svaddr.sun_path, server_path, sizeof(svaddr.sun_path) - 1);

        if (sendto(sock, cmd, cmd_len, 0, (struct sockaddr *) &svaddr, len) != cmd_len)
                LOG("sendto\n");

        return 0;
}

static int create_client_sock(char *name)
{
        struct sockaddr_un claddr;
        int sfd;
        char path[128];

        snprintf(path, sizeof(path),
                 "%s.%d", name, getpid());

        if (remove(path) == -1 && errno != ENOENT)
                LOG("remove unix sock data path\n");

        /* Create  socket; bind to unique pathname */
        sfd = socket(AF_UNIX, SOCK_DGRAM, 0);
        if (sfd == -1)
                LOG("create unix socket fail\n");

        memset(&claddr, 0, sizeof(struct sockaddr_un));
        claddr.sun_family = AF_UNIX;
        snprintf(&claddr.sun_path[1], sizeof(claddr.sun_path)-2,
                 "%s", path);

        if (bind(sfd, (struct sockaddr *) &claddr, sizeof(struct sockaddr_un)) == -1)
            LOG("bind error %s\n", name);

        return sfd;
}


static void hexdump(void *buf, long size)
{
	char sz_buf[100];
	long indent = 1;
	long out_len, index, out_len2;
	long rel_pos;
	struct {
		char *data;
		unsigned long size;
	} buff;
	unsigned char *tmp,tmp_pos;
	unsigned char *addr = (unsigned char *)buf;

	buff.data = (char *)addr;
	buff.size = size;

	while (buff.size > 0) {
		tmp      = (unsigned char *)buff.data;
		out_len  = (int)buff.size;
		if (out_len > 32)
			out_len = 32;

		/* create a 85-character formatted output line: */
		sprintf(sz_buf, "                              "
			"                              "
			"              [%08lX]", tmp-addr);
		out_len2 = out_len;

		for (index=indent, rel_pos=0; out_len2; out_len2--,index += 2 ) {
			tmp_pos = *tmp++;
			sprintf(sz_buf + index, "%02X ", (unsigned short)tmp_pos);
			if (!(++rel_pos & 3))     /* extra blank after 4 bytes */
				index++;
		}

		if (!(rel_pos & 3)) index--;

		sz_buf[index+1] = ' ';

		LOG("%s\n", sz_buf);

		buff.data += out_len;
		buff.size -= out_len;
	}
}

#define APP_NAME		"sniffex"
#define APP_DESC		"Sniffer example using libpcap"
#define APP_COPYRIGHT	"Copyright (c) 2005 The Tcpdump Group"
#define APP_DISCLAIMER	"THERE IS ABSOLUTELY NO WARRANTY FOR THIS PROGRAM."

#include <pcap.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

/* default snap length (maximum bytes per packet to capture) */
#define SNAP_LEN 1518

/* ethernet headers are always exactly 14 bytes [1] */
#define SIZE_ETHERNET 14

/* Ethernet addresses are 6 bytes */
#define ETHER_ADDR_LEN	6

/* Ethernet header */
struct sniff_ethernet {
        u_char  ether_dhost[ETHER_ADDR_LEN];    /* destination host address */
        u_char  ether_shost[ETHER_ADDR_LEN];    /* source host address */
        u_short ether_type;                     /* IP? ARP? RARP? etc */
};

/* IP header */
struct sniff_ip {
        u_char  ip_vhl;                 /* version << 4 | header length >> 2 */
        u_char  ip_tos;                 /* type of service */
        u_short ip_len;                 /* total length */
        u_short ip_id;                  /* identification */
        u_short ip_off;                 /* fragment offset field */
        #define IP_RF 0x8000            /* reserved fragment flag */
        #define IP_DF 0x4000            /* dont fragment flag */
        #define IP_MF 0x2000            /* more fragments flag */
        #define IP_OFFMASK 0x1fff       /* mask for fragmenting bits */
        u_char  ip_ttl;                 /* time to live */
        u_char  ip_p;                   /* protocol */
        u_short ip_sum;                 /* checksum */
        struct  in_addr ip_src,ip_dst;  /* source and dest address */
};
#define IP_HL(ip)               (((ip)->ip_vhl) & 0x0f)
#define IP_V(ip)                (((ip)->ip_vhl) >> 4)

/* TCP header */
typedef u_int tcp_seq;

struct sniff_tcp {
        u_short th_sport;               /* source port */
        u_short th_dport;               /* destination port */
        tcp_seq th_seq;                 /* sequence number */
        tcp_seq th_ack;                 /* acknowledgement number */
        u_char  th_offx2;               /* data offset, rsvd */
#define TH_OFF(th)      (((th)->th_offx2 & 0xf0) >> 4)
        u_char  th_flags;
        #define TH_FIN  0x01
        #define TH_SYN  0x02
        #define TH_RST  0x04
        #define TH_PUSH 0x08
        #define TH_ACK  0x10
        #define TH_URG  0x20
        #define TH_ECE  0x40
        #define TH_CWR  0x80
        #define TH_FLAGS        (TH_FIN|TH_SYN|TH_RST|TH_ACK|TH_URG|TH_ECE|TH_CWR)
        u_short th_win;                 /* window */
        u_short th_sum;                 /* checksum */
        u_short th_urp;                 /* urgent pointer */
};

void
got_packet(u_char *args, const struct pcap_pkthdr *header, u_char *packet);

void
print_payload(u_char *payload, int len);

void
print_hex_ascii_line(u_char *payload, int len, int offset);

void
print_app_banner(void);

void
print_app_usage(void);

/*
 * app name/banner
 */
void
print_app_banner(void)
{

	LOG("%s - %s\n", APP_NAME, APP_DESC);
	LOG("%s\n", APP_COPYRIGHT);
	LOG("%s\n", APP_DISCLAIMER);
	LOG("\n");

        return;
}

/*
 * print help text
 */
void
print_app_usage(void)
{

	LOG("Usage: %s [interface]\n", APP_NAME);
	LOG("\n");
	LOG("Options:\n");
	LOG("    interface    Listen on <interface> for packets.\n");
	LOG("\n");

        return;
}

/*
 * print data in rows of 16 bytes: offset   hex   ascii
 *
 * 00000   47 45 54 20 2f 20 48 54  54 50 2f 31 2e 31 0d 0a   GET / HTTP/1.1..
 */
void
print_hex_ascii_line(u_char *payload, int len, int offset)
{

	int i;
	int gap;
	u_char *ch;

	/* offset */
	LOG("%05d   ", offset);

	/* hex */
	ch = payload;
	for(i = 0; i < len; i++) {
		LOG("%02x ", *ch);
		ch++;
		/* print extra space after 8th byte for visual aid */
		if (i == 7)
			LOG(" ");
	}
	/* print space to handle line less than 8 bytes */
	if (len < 8)
		LOG(" ");

	/* fill hex gap with spaces if not full line */
	if (len < 16) {
		gap = 16 - len;
		for (i = 0; i < gap; i++) {
			LOG("   ");
		}
	}
	LOG("   ");

	/* ascii (if printable) */
	ch = payload;
	for(i = 0; i < len; i++) {
		if (isprint(*ch))
			LOG("%c", *ch);
		else {
			LOG(".");
                        /* change with "." for no-display char */
                        *ch = '.';
                }
		ch++;
	}

	LOG("\n");

        return;
}

/*
 * print packet payload data (avoid printing binary data)
 */
void
print_payload(u_char *payload, int len)
{

	int len_rem = len;
	int line_width = 16;			/* number of bytes per line */
	int line_len;
	int offset = 0;					/* zero-based offset counter */
	u_char *ch = payload;

	if (len <= 0)
		return;

	/* data fits on one line */
	if (len <= line_width) {
		print_hex_ascii_line(ch, len, offset);
		return;
	}

	/* data spans multiple lines */
	for ( ;; ) {
		/* compute current line length */
		line_len = line_width % len_rem;
		/* print line */
		print_hex_ascii_line(ch, line_len, offset);
		/* compute total remaining */
		len_rem = len_rem - line_len;
		/* shift pointer to remaining bytes to print */
		ch = ch + line_len;
		/* add offset */
		offset = offset + line_width;
		/* check if we have line width chars or less */
		if (len_rem <= line_width) {
			/* print last line and get out */
			print_hex_ascii_line(ch, len_rem, offset);
			break;
		}
	}

        return;
}

/* matchhere: search for regexp at beginning of text */
int matchhere(char *regexp, char *text)
{
	if (regexp[0] == '\0')
		return 1;
	if (regexp[1] == '*')
		return matchstar(regexp[0], regexp+2, text);
	if (regexp[0] == '$' && regexp[1] == '\0')
		return *text == '\0';
	if (*text!='\0' && (regexp[0]=='.' || regexp[0]==*text))
		return matchhere(regexp+1, text+1);
	return 0;
}

/* match: search for regexp anywhere in text */
int match(char *regexp, char *text)
{
	if (regexp[0] == '^')
		return matchhere(regexp+1, text);
	do {	/* must look even if string is empty */
		if (matchhere(regexp, text))
			return 1;
	} while (*text++ != '\0');
	return 0;
}

/* matchstar: search for c*regexp at beginning of text */
int matchstar(int c, char *regexp, char *text)
{
	do {	/* a * matches zero or more instances */
		if (matchhere(regexp, text))
			return 1;
	} while (*text != '\0' && (*text++ == c || c == '.'));
	return 0;
}

#include <sys/socket.h>
#include <sys/ioctl.h>
#include <linux/if.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

static u_char old_mac[ETHER_ADDR_LEN] =  {0};

/*
 * dissect/print packet
 */
void
got_packet(u_char *args, const struct pcap_pkthdr *header, u_char *packet)
{

	static int count = 1;                   /* packet counter */

	/* declare pointers to packet headers */
	const struct sniff_ethernet *ethernet;  /* The ethernet header [1] */
	const struct sniff_ip *ip;              /* The IP header */
	const struct sniff_tcp *tcp;            /* The TCP header */
	const char *payload;                    /* Packet payload */

	int size_ip;
	int size_tcp;
	int size_payload;

	LOG("\nPacket number %d:\n", count);

	/* define ethernet header */
	ethernet = (struct sniff_ethernet*)(packet);

	/* define/compute ip header offset */
	ip = (struct sniff_ip *)(packet + SIZE_ETHERNET);
	size_ip = IP_HL(ip)*4;
	if (size_ip < 20) {
		LOG("   * Invalid IP header length: %u bytes\n", size_ip);
		return;
	}

	/* print source and destination IP addresses */
	LOG("From: %s -> ", inet_ntoa(ip->ip_src));
	LOG("To: %s ", inet_ntoa(ip->ip_dst));

        /* don't handle the packet mac address is ourself */
        {
                int fd;
                struct ifreq ifr;

                memset(&ifr, 0, sizeof(ifr));

                fd = socket(AF_INET, SOCK_DGRAM, 0);

                ifr.ifr_addr.sa_family = AF_INET;
                strncpy(ifr.ifr_name , args, IFNAMSIZ-1);

                ioctl(fd, SIOCGIFHWADDR, &ifr);
                close(fd);

                if (memcmp(ethernet->ether_shost,
                           ifr.ifr_hwaddr.sa_data, ETHER_ADDR_LEN) == 0)
                        return;
        }

        if (ip->ip_p != IPPROTO_TCP)
                return;

        /* change the old mac, find a new device */
        if (memcmp(ethernet->ether_shost, old_mac, ETHER_ADDR_LEN) != 0) {
                memcpy(old_mac, ethernet->ether_shost, ETHER_ADDR_LEN);

                u_char *mac = old_mac;
                printf("src mac %.2X:%.2X:%.2X:%.2X:%.2X:%.2X\n", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
                uint8_t value[128] =  {0};
                int cfd = create_client_sock(CLIENT);
                snprintf(value, 127, "%02X:%02X:%02X:%02X:%02X:%02X SNIFFER\n",
                         mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
                sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                close(cfd);
        }

        if (ip->ip_p != IPPROTO_TCP)
            return;

        count++;

        /* Send signal per 500 packet */
        if (count%500 == 10) {
                u_char *mac = ethernet->ether_shost;
                LOG("src mac %.2X:%.2X:%.2X:%.2X:%.2X:%.2X\n", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
                uint8_t value[128] =  {0};
                int cfd = create_client_sock(CLIENT);
                snprintf(value, 127, "%02x:%02x:%02x:%02x:%02x:%02x SNIFFER",
                         mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
                sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                close(cfd);

                return;
        }

	/* determine protocol */
	switch(ip->ip_p) {
		case IPPROTO_TCP:
			LOG(" Protocol: TCP");
			break;
		case IPPROTO_UDP:
			LOG(" Protocol: UDP");
			return;
		case IPPROTO_ICMP:
			LOG(" Protocol: ICMP");
			return;
		case IPPROTO_IP:
			LOG(" Protocol: IP");
			return;
		default:
			LOG(" Protocol: unknown");
			return;
	}

	/*
	 *  OK, this packet is TCP.
	 */

	/* define/compute tcp header offset */
	tcp = (struct sniff_tcp *)(packet + SIZE_ETHERNET + size_ip);
	size_tcp = TH_OFF(tcp)*4;
	if (size_tcp < 20) {
		LOG("   * Invalid TCP header length: %u bytes\n", size_tcp);
		return;
	}

	LOG("Src port: %d ", ntohs(tcp->th_sport));
	LOG("Dst port: %d\n", ntohs(tcp->th_dport));

	/* define/compute tcp payload (segment) offset */
	payload = (u_char *)(packet + SIZE_ETHERNET + size_ip + size_tcp);

	/* compute tcp payload (segment) size */
	size_payload = ntohs(ip->ip_len) - (size_ip + size_tcp);

	/*
	 * Print payload data; it might be binary, so don't just
	 * treat it as a string.
	 */
	if (size_payload > 0) {
		LOG("   Payload (%d bytes):\n", size_payload);
		print_payload(payload, size_payload);
	}

        if (match("Services", payload)) {
                u_char *mac = ethernet->ether_shost;
                LOG("Services src mac %02.2x:%02.2x:%02.2x:%02.2x:%02.2x:%02.2x\n", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
                uint8_t value[128] =  {0};
                int cfd = create_client_sock(CLIENT);
                snprintf(value, 127, "%02x:%02x:%02x:%02x:%02x:%02x SNIFFER",
                         mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
                sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                close(cfd);
        }

        return;
}

#if 0
int main(int argc, char **argv)
{
	char *dev = NULL;			/* capture device name */
	char errbuf[PCAP_ERRBUF_SIZE];		/* error buffer */
	pcap_t *handle;				/* packet capture handle */

	char filter_exp[] = "ip host 10.74.208.24";		/* filter expression [3] */
	struct bpf_program fp;			/* compiled filter program (expression) */
	bpf_u_int32 mask;			/* subnet mask */
	bpf_u_int32 net;			/* ip */
	int num_packets = 10;			/* number of packets to capture */

	print_app_banner();

	/* check for capture device name on command-line */
	if (argc == 2) {
		dev = argv[1];
	} else if (argc > 2) {
		fprintf(stderr, "error: unrecognized command-line options\n\n");
		print_app_usage();
		exit(EXIT_FAILURE);
	} else {
		/* find a capture device if not specified on command-line */
		dev = pcap_lookupdev(errbuf);
		if (dev == NULL) {
			fprintf(stderr, "Couldn't find default device: %s\n",
			    errbuf);
			exit(EXIT_FAILURE);
		}
	}

	/* get network number and mask associated with capture device */
	if (pcap_lookupnet(dev, &net, &mask, errbuf) == -1) {
		fprintf(stderr, "Couldn't get netmask for device %s: %s\n",
		    dev, errbuf);
		net = 0;
		mask = 0;
	}

	/* print capture info */
	printf("Device: %s\n", dev);
	printf("Number of packets: %d\n", num_packets);
	printf("Filter expression: %s\n", filter_exp);

	/* open capture device */
	handle = pcap_open_live(dev, SNAP_LEN, 1, 1000, errbuf);
	if (handle == NULL) {
		fprintf(stderr, "Couldn't open device %s: %s\n", dev, errbuf);
		exit(EXIT_FAILURE);
	}

	/* make sure we're capturing on an Ethernet device [2] */
	if (pcap_datalink(handle) != DLT_EN10MB) {
		fprintf(stderr, "%s is not an Ethernet\n", dev);
		exit(EXIT_FAILURE);
	}

	/* compile the filter expression */
	if (pcap_compile(handle, &fp, filter_exp, 0, net) == -1) {
		fprintf(stderr, "Couldn't parse filter %s: %s\n",
		    filter_exp, pcap_geterr(handle));
		exit(EXIT_FAILURE);
	}

	/* apply the compiled filter */
	if (pcap_setfilter(handle, &fp) == -1) {
		fprintf(stderr, "Couldn't install filter %s: %s\n",
		    filter_exp, pcap_geterr(handle));
		exit(EXIT_FAILURE);
	}

	/* now we can set our callback function */
        while(1)
            pcap_loop(handle, num_packets, got_packet, dev);

	/* cleanup */
	pcap_freecode(&fp);
	pcap_close(handle);

	printf("\nCapture complete.\n");

        return 0;
}
#endif

int sniffer(char *devname)
{
	char *dev = NULL;			/* capture device name */
	char errbuf[PCAP_ERRBUF_SIZE];		/* error buffer */
	pcap_t *handle;				/* packet capture handle */

	char filter_exp[] = "ip host 112.74.208.24";		/* filter expression [3] */
	struct bpf_program fp;			/* compiled filter program (expression) */
	bpf_u_int32 mask;			/* subnet mask */
	bpf_u_int32 net;			/* ip */
	int num_packets = 10;			/* number of packets to capture */

	//print_app_banner();

	/* check for capture device name on command-line */
	if (devname) {
		dev = devname;
        } else {
		/* find a capture device if not specified on command-line */
		dev = pcap_lookupdev(errbuf);
		if (dev == NULL) {
			LOG("Couldn't find default device: %s\n",
			    errbuf);
			exit(EXIT_FAILURE);
		}
	}

	/* get network number and mask associated with capture device */
	if (pcap_lookupnet(dev, &net, &mask, errbuf) == -1) {
		LOG("Couldn't get netmask for device %s: %s\n",
		    dev, errbuf);
		net = 0;
		mask = 0;
	}

	/* print capture info */
	LOG("Device: %s\n", dev);
	LOG("Number of packets: %d\n", num_packets);
	LOG("Filter expression: %s\n", filter_exp);

	/* open capture device */
	handle = pcap_open_live(dev, SNAP_LEN, 1, 1000, errbuf);
	if (handle == NULL) {
		LOG("Couldn't open device %s: %s\n", dev, errbuf);
		exit(EXIT_FAILURE);
	}

	/* make sure we're capturing on an Ethernet device [2] */
	if (pcap_datalink(handle) != DLT_EN10MB) {
		LOG("%s is not an Ethernet\n", dev);
		exit(EXIT_FAILURE);
	}

	/* compile the filter expression */
	if (pcap_compile(handle, &fp, filter_exp, 0, net) == -1) {
		LOG("Couldn't parse filter %s: %s\n",
		    filter_exp, pcap_geterr(handle));
		exit(EXIT_FAILURE);
	}

	/* apply the compiled filter */
	if (pcap_setfilter(handle, &fp) == -1) {
		LOG("Couldn't install filter %s: %s\n",
		    filter_exp, pcap_geterr(handle));
		exit(EXIT_FAILURE);
	}

	/* now we can set our callback function */
        while(1)
            pcap_loop(handle, num_packets, got_packet, dev);

	/* cleanup */
	pcap_freecode(&fp);
	pcap_close(handle);

	LOG("\nCapture complete.\n");

        return 0;
}

/**
 * print prompt
 */
static void print_prompt(void)
{
	LOG(COLOR_BLUE "[GATT client]" COLOR_OFF "# ");
	fflush(stdout);
}

/**
 * convert error code to string
 *
 * @param ecode	error code (BT_ATT mostly)
 * @return 		ascii string full english ecode label
 */
static const char *ecode_to_string(uint8_t ecode)
{
	switch (ecode) {
	case BT_ATT_ERROR_INVALID_HANDLE:
		return "Invalid Handle";
	case BT_ATT_ERROR_READ_NOT_PERMITTED:
		return "Read Not Permitted";
	case BT_ATT_ERROR_WRITE_NOT_PERMITTED:
		return "Write Not Permitted";
	case BT_ATT_ERROR_INVALID_PDU:
		return "Invalid PDU";
	case BT_ATT_ERROR_AUTHENTICATION:
		return "Authentication Required";
	case BT_ATT_ERROR_REQUEST_NOT_SUPPORTED:
		return "Request Not Supported";
	case BT_ATT_ERROR_INVALID_OFFSET:
		return "Invalid Offset";
	case BT_ATT_ERROR_AUTHORIZATION:
		return "Authorization Required";
	case BT_ATT_ERROR_PREPARE_QUEUE_FULL:
		return "Prepare Write Queue Full";
	case BT_ATT_ERROR_ATTRIBUTE_NOT_FOUND:
		return "Attribute Not Found";
	case BT_ATT_ERROR_ATTRIBUTE_NOT_LONG:
		return "Attribute Not Long";
	case BT_ATT_ERROR_INSUFFICIENT_ENCRYPTION_KEY_SIZE:
		return "Insuficient Encryption Key Size";
	case BT_ATT_ERROR_INVALID_ATTRIBUTE_VALUE_LEN:
		return "Invalid Attribute value len";
	case BT_ATT_ERROR_UNLIKELY:
		return "Unlikely Error";
	case BT_ATT_ERROR_INSUFFICIENT_ENCRYPTION:
		return "Insufficient Encryption";
	case BT_ATT_ERROR_UNSUPPORTED_GROUP_TYPE:
		return "Group type Not Supported";
	case BT_ATT_ERROR_INSUFFICIENT_RESOURCES:
		return "Insufficient Resources";
	case BT_ERROR_CCC_IMPROPERLY_CONFIGURED:
		return "CCC Improperly Configured";
	case BT_ERROR_ALREADY_IN_PROGRESS:
		return "Procedure Already in Progress";
	case BT_ERROR_OUT_OF_RANGE:
		return "Out of Range";
	default:
		return "Unknown error type";
	}
}

/**
 * disconnect callback, quit mainloop
 *
 * @param err		error code associated with disconnect
 * @param user_data	user data pointer (not used)
 */
static void att_disconnect_cb(int err, void *user_data)
{
	LOG("Device disconnected: %s\n", strerror(err));

	mainloop_quit();
}

/**
 * print a prefix (user_data) followed by a message (str)
 * example att: ATT op 0x02 (att: is the prefix)
 *
 * @param str		message to print
 * @param user_data pointer to prefix
 */
static void att_debug_cb(const char *str, void *user_data)
{
	const char *prefix = user_data;
	PRLOG(COLOR_BOLDGRAY "%s" COLOR_BOLDWHITE "%s\n" COLOR_OFF, prefix, str);
}

/**
 * print a prefix (user_data) followed by a message (str)
 * example gatt: MTU exchange complete, with MTU: 23 (gatt: is the prefix)
 *
 * @param str		message to print
 * @param user_data	pointer to prefix
 */
static void gatt_debug_cb(const char *str, void *user_data)
{
	const char *prefix = user_data;

	PRLOG(COLOR_GREEN "%s%s\n" COLOR_OFF, prefix, str);
}

static void ready_cb(bool success, uint8_t att_ecode, void *user_data);
static void service_changed_cb(uint16_t start_handle, uint16_t end_handle,
							void *user_data);

/**
 * log discovered service
 *
 * @param attr	gatt_db_attribute structure (service data)
 * @param str	comment about the logged service ("Service added", "Service removed"...)
 */
static void log_service_event(struct gatt_db_attribute *attr, const char *str)
{
	char uuid_str[MAX_LEN_UUID_STR];
	bt_uuid_t uuid;
	uint16_t start, end;

	gatt_db_attribute_get_service_uuid(attr, &uuid);
	bt_uuid_to_string(&uuid, uuid_str, sizeof(uuid_str));

	gatt_db_attribute_get_service_handles(attr, &start, &end);

	PRLOG("%s - UUID: %s start: 0x%04x end: 0x%04x\n", str, uuid_str,
								start, end);
}

/**
 * service added callback
 *
 * @param attr
 * @param user_data
 */
static void service_added_cb(struct gatt_db_attribute *attr, void *user_data)
{
	log_service_event(attr, "Service Added");
}

/**
 * service removed callback
 *
 * @param attr
 * @param user_data
 */
static void service_removed_cb(struct gatt_db_attribute *attr, void *user_data)
{
	log_service_event(attr, "Service Removed");
}

/**
 * create an gatt client attached to the fd l2cap socket
 *
 * @param fd	socket
 * @param mtu	selected pdu size
 * @return gatt client structure
 */
static struct client *client_create(int fd, uint16_t mtu)
{
	struct client *cli;

	cli = new0(struct client, 1);
	if (!cli) {
		fprintf(stderr, "Failed to allocate memory for client\n");
		return NULL;
	}

	cli->att = bt_att_new(fd, false);
	if (!cli->att) {
		fprintf(stderr, "Failed to initialze ATT transport layer\n");
		bt_att_unref(cli->att);
		free(cli);
		return NULL;
	}

	if (!bt_att_set_close_on_unref(cli->att, true)) {
		fprintf(stderr, "Failed to set up ATT transport layer\n");
		bt_att_unref(cli->att);
		free(cli);
		return NULL;
	}

	if (!bt_att_register_disconnect(cli->att, att_disconnect_cb, NULL,
								NULL)) {
		fprintf(stderr, "Failed to set ATT disconnect handler\n");
		bt_att_unref(cli->att);
		free(cli);
		return NULL;
	}

	cli->fd = fd;
	cli->db = gatt_db_new();
	if (!cli->db) {
		fprintf(stderr, "Failed to create GATT database\n");
		bt_att_unref(cli->att);
		free(cli);
		return NULL;
	}

	cli->gatt = bt_gatt_client_new(cli->db, cli->att, mtu);
	if (!cli->gatt) {
		fprintf(stderr, "Failed to create GATT client\n");
		gatt_db_unref(cli->db);
		bt_att_unref(cli->att);
		free(cli);
		return NULL;
	}

	gatt_db_register(cli->db, service_added_cb, service_removed_cb,
								NULL, NULL);

	if (verbose) {
		bt_att_set_debug(cli->att, att_debug_cb, "att: ", NULL);
		bt_gatt_client_set_debug(cli->gatt, gatt_debug_cb, "gatt: ",
									NULL);
	}

	bt_gatt_client_set_ready_handler(cli->gatt, ready_cb, cli, NULL);
	bt_gatt_client_set_service_changed(cli->gatt, service_changed_cb, cli,
									NULL);

	/* bt_gatt_client already holds a reference */
	gatt_db_unref(cli->db);

	return cli;
}

/**
 * client structure cleanup
 *
 * @param cli client pointer to destroy
 */
static void client_destroy(struct client *cli)
{
	bt_gatt_client_unref(cli->gatt);
	bt_att_unref(cli->att);
	free(cli);
}

/**
 * printing bt_uuid_t structure (uuid)
 *
 * @param uuid
 */
static void print_uuid(const bt_uuid_t *uuid)
{
	char uuid_str[MAX_LEN_UUID_STR];
	bt_uuid_t uuid128;

	bt_uuid_to_uuid128(uuid, &uuid128);
	bt_uuid_to_string(&uuid128, uuid_str, sizeof(uuid_str));

	LOG("%s\n", uuid_str);
}

/**
 * print included data
 *
 * @param attr			gatt_db_attribute to print
 * @param user_data		client structure pointer
 */
static void print_incl(struct gatt_db_attribute *attr, void *user_data)
{
	struct client *cli = user_data;
	uint16_t handle, start, end;
	struct gatt_db_attribute *service;
	bt_uuid_t uuid;

	if (!gatt_db_attribute_get_incl_data(attr, &handle, &start, &end))
		return;

	service = gatt_db_get_attribute(cli->db, start);
	if (!service)
		return;

	gatt_db_attribute_get_service_uuid(service, &uuid);

	LOG("\t  " COLOR_GREEN "include" COLOR_OFF " - handle: "
					"0x%04x, - start: 0x%04x, end: 0x%04x,"
					"uuid: ", handle, start, end);
	print_uuid(&uuid);
}

/**
 * print attribute uuid
 *
 * @param attr
 * @param user_data
 */
static void print_desc(struct gatt_db_attribute *attr, void *user_data)
{
	LOG("\t\t  " COLOR_MAGENTA "descr" COLOR_OFF
					" - handle: 0x%04x, uuid: ",
					gatt_db_attribute_get_handle(attr));
	print_uuid(gatt_db_attribute_get_type(attr));
}

/**
 * print characteristic
 *
 * @param attr
 * @param user_data
 */
static void print_chrc(struct gatt_db_attribute *attr, void *user_data)
{
	uint16_t handle, value_handle;
	uint8_t properties;
	bt_uuid_t uuid;

	if (!gatt_db_attribute_get_char_data(attr, &handle,
								&value_handle,
								&properties,
								&uuid))
		return;

	LOG("\t  " COLOR_YELLOW "charac" COLOR_OFF
					" - start: 0x%04x, value: 0x%04x, "
					"props: 0x%02x, uuid: ",
					handle, value_handle, properties);
	print_uuid(&uuid);

	gatt_db_service_foreach_desc(attr, print_desc, NULL);
}

/**
 * print service
 *
 * @param attr
 * @param user_data
 */
static void print_service(struct gatt_db_attribute *attr, void *user_data)
{
	struct client *cli = user_data;
	uint16_t start, end;
	bool primary;
	bt_uuid_t uuid;

	if (!gatt_db_attribute_get_service_data(attr, &start, &end, &primary,
									&uuid))
		return;

	LOG(COLOR_RED "service" COLOR_OFF " - start: 0x%04x, "
				"end: 0x%04x, type: %s, uuid: ",
				start, end, primary ? "primary" : "secondary");
	print_uuid(&uuid);

	gatt_db_service_foreach_incl(attr, print_incl, cli);
	gatt_db_service_foreach_char(attr, print_chrc, NULL);

	LOG("\n");
}

/**
 * print the list of services
 *
 * @param cli	client pointer
 */
static void print_services(struct client *cli)
{
	LOG("\n");

	gatt_db_foreach_service(cli->db, NULL, print_service, cli);
}

/**
 * print services providing the uuid
 *
 * @param cli
 * @param uuid
 */
static void print_services_by_uuid(struct client *cli, const bt_uuid_t *uuid)
{
	LOG("\n");

	gatt_db_foreach_service(cli->db, uuid, print_service, cli);
}

/**
 * print services providing the handle
 *
 * @param cli
 * @param handle
 */
static void print_services_by_handle(struct client *cli, uint16_t handle)
{
	LOG("\n");

	/* TODO: Filter by handle */
	gatt_db_foreach_service(cli->db, NULL, print_service, cli);
}

/**
 * GATT discovery procedures call back
 *
 * @param success		if not 0 an error occured
 * @param att_ecode		att error code
 * @param user_data		pointer to client structure
 */
static void ready_cb(bool success, uint8_t att_ecode, void *user_data)
{
	struct client *cli = user_data;

	if (!success) {
		PRLOG("GATT discovery procedures failed - error code: 0x%02x\n",
								att_ecode);
		return;
	}

	PRLOG("GATT discovery procedures complete\n");

	print_services(cli);
	print_prompt();

        char cmd[128] = {0};
        int cfd = create_client_sock(CLIENT);
        snprintf(cmd, 127, "%s CONNECT sucess", buf+8);
        sock_send_cmd(cfd, SERVER, cmd, strlen(cmd)+1);
        close(cfd);
}

/**
 * service changed call back
 *
 * @param start_handle
 * @param end_handle
 * @param user_data		client pointer
 */
static void service_changed_cb(uint16_t start_handle, uint16_t end_handle,
								void *user_data)
{
	struct client *cli = user_data;

	LOG("\nService Changed handled - start: 0x%04x end: 0x%04x\n",
						start_handle, end_handle);

	gatt_db_foreach_service_in_range(cli->db, NULL, print_service, cli,
						start_handle, end_handle);
	print_prompt();
}

/**
 * services usage (services --help to learn options)
 */
static void services_usage(void)
{
	LOG("Usage: services [options]\nOptions:\n"
		"\t -u, --uuid <uuid>\tService UUID\n"
		"\t -a, --handle <handle>\tService start handle\n"
		"\t -h, --help\t\tShow help message\n"
		"e.g.:\n"
		"\tservices\n\tservices -u 0x180d\n\tservices -a 0x0009\n");
}

/**
 * parse command string
 *
 * @param str			command to parse
 * @param expected_argc	number of arguments expected
 * @param argv			pointers to arguments separated by space or tab
 * @param argc			argument counter (and actual count)
 * @return				true = success false = error
 */
static bool parse_args(char *str, int expected_argc,  char **argv, int *argc)
{
	char **ap;

	for (ap = argv; (*ap = strsep(&str, " \t")) != NULL;) {
		if (**ap == '\0')
			continue;

		(*argc)++;
		ap++;

		if (*argc > expected_argc)
			return false;
	}

	return true;
}

/**
 * command interpreter
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	one of the possible command (help to get a list)
 * 					&lt;command&gt; --help to have a help on that command
 */
static void cmd_services(struct client *cli, char *cmd_str)
{
	char *argv[3];
	int argc = 0;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 2, argv, &argc)) {
		services_usage();
		return;
	}

	if (!argc) {
		print_services(cli);
		return;
	}

	if (argc != 2) {
		services_usage();
		return;
	}

	if (!strcmp(argv[0], "-u") || !strcmp(argv[0], "--uuid")) {
		bt_uuid_t tmp, uuid;

		if (bt_string_to_uuid(&tmp, argv[1]) < 0) {
			LOG("Invalid UUID: %s\n", argv[1]);
			return;
		}

		bt_uuid_to_uuid128(&tmp, &uuid);

		print_services_by_uuid(cli, &uuid);
	} else if (!strcmp(argv[0], "-a") || !strcmp(argv[0], "--handle")) {
		uint16_t handle;
		char *endptr = NULL;

		handle = strtol(argv[1], &endptr, 0);
		if (!endptr || *endptr != '\0') {
			LOG("Invalid start handle: %s\n", argv[1]);
			return;
		}

		print_services_by_handle(cli, handle);
	} else
		services_usage();
}

/**
 * read multiple usage
 */
static void read_multiple_usage(void)
{
	LOG("Usage: read-multiple <handle_1> <handle_2> ...\n");
}

/**
 * read multiple callback
 *
 * @param success		==0 => print error, <>0 print values
 * @param att_ecode 	att error code
 * @param value			vector of values
 * @param length		number of values
 * @param user_data		not used
 */
static void read_multiple_cb(bool success, uint8_t att_ecode,
					const uint8_t *value, uint16_t length,
					void *user_data)
{
	int i;

	if (!success) {
		PRLOG("\nRead multiple request failed: 0x%02x\n", att_ecode);
		return;
	}

	LOG("\nRead multiple value (%u bytes):", length);

	for (i = 0; i < length; i++)
		LOG("%02x ", value[i]);

	PRLOG("\n");
}

/**
 * read multiple command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	command string for read multiple
 */
static void cmd_read_multiple(struct client *cli, char *cmd_str)
{
	int argc = 0;
	uint16_t *value;
	char *argv[512];
	int i;
	char *endptr = NULL;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, sizeof(argv), argv, &argc) || argc < 2) {
		read_multiple_usage();
		return;
	}

	value = malloc(sizeof(uint16_t) * argc);
	if (!value) {
		LOG("Failed to construct value\n");
		return;
	}

	for (i = 0; i < argc; i++) {
		value[i] = strtol(argv[i], &endptr, 0);
		if (endptr == argv[i] || *endptr != '\0' || !value[i]) {
			LOG("Invalid value byte: %s\n", argv[i]);
			free(value);
			return;
		}
	}

	if (!bt_gatt_client_read_multiple(cli->gatt, value, argc,
						read_multiple_cb, NULL, NULL))
		LOG("Failed to initiate read multiple procedure\n");

	free(value);
}

/**
 * read value usage
 */
static void read_value_usage(void)
{
	LOG("Usage: read-value <value_handle>\n");
}

/**
 * read value callback
 *
 * @param success		==0 => print error, <>0 print value
 * @param att_ecode		att error code
 * @param value			vector of values
 * @param length		size of vector
 * @param user_data		not used
 */
static void read_cb(bool success, uint8_t att_ecode, const uint8_t *value,
					uint16_t length, void *user_data)
{
	int i;

	if (!success) {
		PRLOG("\nRead request failed: %s (0x%02x)\n",
				ecode_to_string(att_ecode), att_ecode);
		return;
	}

	LOG("\nRead value");

	if (length == 0) {
		PRLOG(": 0 bytes\n");
		return;
	}

	LOG(" (%u bytes): ", length);

	for (i = 0; i < length; i++)
		LOG("%02x ", value[i]);

	PRLOG("\n");
}

/**
 * read value command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	command string for read value
 */
static void cmd_read_value(struct client *cli, char *cmd_str)
{
	char *argv[2];
	int argc = 0;
	uint16_t handle;
	char *endptr = NULL;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 1, argv, &argc) || argc != 1) {
		read_value_usage();
		return;
	}

	handle = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !handle) {
		LOG("Invalid value handle: %s\n", argv[0]);
		return;
	}

	if (!bt_gatt_client_read_value(cli->gatt, handle, read_cb,
								NULL, NULL))
		LOG("Failed to initiate read value procedure\n");
}

/**
 *  read long value usage
 */
static void read_long_value_usage(void)
{
	LOG("Usage: read-long-value <value_handle> <offset>\n");
}

/**
 * read long value command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	command string for read long value
 */
static void cmd_read_long_value(struct client *cli, char *cmd_str)
{
	char *argv[3];
	int argc = 0;
	uint16_t handle;
	uint16_t offset;
	char *endptr = NULL;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 2, argv, &argc) || argc != 2) {
		read_long_value_usage();
		return;
	}

	handle = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !handle) {
		LOG("Invalid value handle: %s\n", argv[0]);
		return;
	}

	endptr = NULL;
	offset = strtol(argv[1], &endptr, 0);
	if (!endptr || *endptr != '\0') {
		LOG("Invalid offset: %s\n", argv[1]);
		return;
	}

	if (!bt_gatt_client_read_long_value(cli->gatt, handle, offset, read_cb,
								NULL, NULL))
		LOG("Failed to initiate read long value procedure\n");
}

/**
 * write value usage
 */
static void write_value_usage(void)
{
	LOG("Usage: write-value [options] <value_handle> <value>\n"
		"Options:\n"
		"\t-w, --without-response\tWrite without response\n"
		"\t-s, --signed-write\tSigned write command\n"
		"e.g.:\n"
		"\twrite-value 0x0001 00 01 00\n");
}

static struct option write_value_options[] = {
	{ "without-response",	0, 0, 'w' },
	{ "signed-write",	0, 0, 's' },
	{ }
};

/**
 * write value call back
 *
 * @param success		==0 => print error, <>0 print value
 * @param att_ecode		att error code
 * @param user_data		not used
 */
static void write_cb(bool success, uint8_t att_ecode, void *user_data)
{
	if (success) {
		PRLOG("\nWrite successful\n");
	} else {
		PRLOG("\nWrite failed: %s (0x%02x)\n",
				ecode_to_string(att_ecode), att_ecode);
	}
}

/**
 * write value command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	command string for write value
 */
static void cmd_write_value(struct client *cli, char *cmd_str)
{
	int opt, i;
	char *argvbuf[516];
	char **argv = argvbuf;
	int argc = 1;
	uint16_t handle;
	char *endptr = NULL;
	int length;
	uint8_t *value = NULL;
	bool without_response = false;
	bool signed_write = false;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 514, argv + 1, &argc)) {
		LOG("Too many arguments\n");
		write_value_usage();
		return;
	}

	optind = 0;
	argv[0] = "write-value";
	while ((opt = getopt_long(argc, argv, "+ws", write_value_options,
								NULL)) != -1) {
		switch (opt) {
		case 'w':
			without_response = true;
			break;
		case 's':
			signed_write = true;
			break;
		default:
			write_value_usage();
			return;
		}
	}

	argc -= optind;
	argv += optind;

	if (argc < 1) {
		write_value_usage();
		return;
	}

	handle = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !handle) {
		LOG("Invalid handle: %s\n", argv[0]);
		return;
	}

	length = argc - 1;

	if (length > 0) {
		if (length > UINT16_MAX) {
			LOG("Write value too long\n");
			return;
		}

		value = malloc(length);
		if (!value) {
			LOG("Failed to construct write value\n");
			return;
		}

		for (i = 1; i < argc; i++) {
			if (strlen(argv[i]) != 2) {
				LOG("Invalid value byte: %s\n",
								argv[i]);
				goto done;
			}

			value[i-1] = strtol(argv[i], &endptr, 0);
			if (endptr == argv[i] || *endptr != '\0'
							|| errno == ERANGE) {
				LOG("Invalid value byte: %s\n",
								argv[i]);
				goto done;
			}
		}
	}

	if (without_response) {
		if (!bt_gatt_client_write_without_response(cli->gatt, handle,
						signed_write, value, length)) {
			LOG("Failed to initiate write without response "
								"procedure\n");
			goto done;
		}

		LOG("Write command sent\n");
		goto done;
	}

	if (!bt_gatt_client_write_value(cli->gatt, handle, value, length,
								write_cb,
								NULL, NULL))
		LOG("Failed to initiate write procedure\n");

done:
	free(value);
}

/**
 * write long value usage
 */
static void write_long_value_usage(void)
{
	LOG("Usage: write-long-value [options] <value_handle> <offset> "
				"<value>\n"
				"Options:\n"
				"\t-r, --reliable-write\tReliable write\n"
				"e.g.:\n"
				"\twrite-long-value 0x0001 0 00 01 00\n");
}

static struct option write_long_value_options[] = {
	{ "reliable-write",	0, 0, 'r' },
	{ }
};

/**
 * write long call back
 *
 * @param success			==0 => print error, <>0 print value
 * @param reliable_error	status of the write operation when failed
 * @param att_ecode			att error code
 * @param user_data			not used
 */
static void write_long_cb(bool success, bool reliable_error, uint8_t att_ecode,
								void *user_data)
{
	if (success) {
		PRLOG("Write successful\n");
	} else if (reliable_error) {
		PRLOG("Reliable write not verified\n");
	} else {
		PRLOG("\nWrite failed: %s (0x%02x)\n",
				ecode_to_string(att_ecode), att_ecode);
	}
}

/**
 * write long value command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	command string for write long value
 */
static void cmd_write_long_value(struct client *cli, char *cmd_str)
{
	int opt, i;
	char *argvbuf[516];
	char **argv = argvbuf;
	int argc = 1;
	uint16_t handle;
	uint16_t offset;
	char *endptr = NULL;
	int length;
	uint8_t *value = NULL;
	bool reliable_writes = false;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 514, argv + 1, &argc)) {
		LOG("Too many arguments\n");
		write_value_usage();
		return;
	}

	optind = 0;
	argv[0] = "write-long-value";
	while ((opt = getopt_long(argc, argv, "+r", write_long_value_options,
								NULL)) != -1) {
		switch (opt) {
		case 'r':
			reliable_writes = true;
			break;
		default:
			write_long_value_usage();
			return;
		}
	}

	argc -= optind;
	argv += optind;

	if (argc < 2) {
		write_long_value_usage();
		return;
	}

	handle = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !handle) {
		LOG("Invalid handle: %s\n", argv[0]);
		return;
	}

	endptr = NULL;
	offset = strtol(argv[1], &endptr, 0);
	if (!endptr || *endptr != '\0' || errno == ERANGE) {
		LOG("Invalid offset: %s\n", argv[1]);
		return;
	}

	length = argc - 2;

	if (length > 0) {
		if (length > UINT16_MAX) {
			LOG("Write value too long\n");
			return;
		}

		value = malloc(length);
		if (!value) {
			LOG("Failed to construct write value\n");
			return;
		}

		for (i = 2; i < argc; i++) {
			if (strlen(argv[i]) != 2) {
				LOG("Invalid value byte: %s\n",
								argv[i]);
				free(value);
				return;
			}

			value[i-2] = strtol(argv[i], &endptr, 0);
			if (endptr == argv[i] || *endptr != '\0'
							|| errno == ERANGE) {
				LOG("Invalid value byte: %s\n",
								argv[i]);
				free(value);
				return;
			}
		}
	}

	if (!bt_gatt_client_write_long_value(cli->gatt, reliable_writes, handle,
							offset, value, length,
							write_long_cb,
							NULL, NULL))
		LOG("Failed to initiate long write procedure\n");

	free(value);
}

/**
 * write prepare usage
 */
static void write_prepare_usage(void)
{
	LOG("Usage: write-prepare [options] <value_handle> <offset> "
				"<value>\n"
				"Options:\n"
				"\t-s, --session-id\tSession id\n"
				"e.g.:\n"
				"\twrite-prepare -s 1 0x0001 00 01 00\n");
}

static struct option write_prepare_options[] = {
	{ "session-id",		1, 0, 's' },
	{ }
};

/**
 * write prepare command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	write prepare command string
 */
static void cmd_write_prepare(struct client *cli, char *cmd_str)
{
	int opt, i;
	char *argvbuf[516];
	char **argv = argvbuf;
	int argc = 0;
	unsigned int id = 0;
	uint16_t handle;
	uint16_t offset;
	char *endptr = NULL;
	unsigned int length;
	uint8_t *value = NULL;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 514, argv + 1, &argc)) {
		LOG("Too many arguments\n");
		write_value_usage();
		return;
	}

	/* Add command name for getopt_long */
	argc++;
	argv[0] = "write-prepare";

	optind = 0;
	while ((opt = getopt_long(argc, argv , "s:", write_prepare_options,
								NULL)) != -1) {
		switch (opt) {
		case 's':
			if (!optarg) {
				write_prepare_usage();
				return;
			}

			id = atoi(optarg);

			break;
		default:
			write_prepare_usage();
			return;
		}
	}

	argc -= optind;
	argv += optind;

	if (argc < 3) {
		write_prepare_usage();
		return;
	}

	if (cli->reliable_session_id != id) {
		LOG("Session id != Ongoing session id (%u!=%u)\n", id,
						cli->reliable_session_id);
		return;
	}

	handle = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !handle) {
		LOG("Invalid handle: %s\n", argv[0]);
		return;
	}

	endptr = NULL;
	offset = strtol(argv[1], &endptr, 0);
	if (!endptr || *endptr != '\0' || errno == ERANGE) {
		LOG("Invalid offset: %s\n", argv[1]);
		return;
	}

	/*
	 * First two arguments are handle and offset. What remains is the value
	 * length
	 */
	length = argc - 2;

	if (length == 0)
		goto done;

	if (length > UINT16_MAX) {
		LOG("Write value too long\n");
		return;
	}

	value = malloc(length);
	if (!value) {
		LOG("Failed to allocate memory for value\n");
		return;
	}

	for (i = 2; i < argc; i++) {
		if (strlen(argv[i]) != 2) {
			LOG("Invalid value byte: %s\n", argv[i]);
			free(value);
			return;
		}

		value[i-2] = strtol(argv[i], &endptr, 0);
		if (endptr == argv[i] || *endptr != '\0' || errno == ERANGE) {
			LOG("Invalid value byte: %s\n", argv[i]);
			free(value);
			return;
		}
	}

done:
	cli->reliable_session_id =
			bt_gatt_client_prepare_write(cli->gatt, id,
							handle, offset,
							value, length,
							write_long_cb, NULL,
							NULL);
	if (!cli->reliable_session_id)
		LOG("Failed to proceed prepare write\n");
	else
		LOG("Prepare write success.\n"
				"Session id: %d to be used on next write\n",
						cli->reliable_session_id);

	free(value);
}

/**
 * write execute usage
 */
static void write_execute_usage(void)
{
	LOG("Usage: write-execute <session_id> <execute>\n"
				"e.g.:\n"
				"\twrite-execute 1 0\n");
}

/**
 * write execute command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	write execute command string
 */
static void cmd_write_execute(struct client *cli, char *cmd_str)
{
	char *argvbuf[516];
	char **argv = argvbuf;
	int argc = 0;
	char *endptr = NULL;
	unsigned int session_id;
	bool execute;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 514, argv, &argc)) {
		LOG("Too many arguments\n");
		write_value_usage();
		return;
	}

	if (argc < 2) {
		write_execute_usage();
		return;
	}

	session_id = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0') {
		LOG("Invalid session id: %s\n", argv[0]);
		return;
	}

	if (session_id != cli->reliable_session_id) {
		LOG("Invalid session id: %u != %u\n", session_id,
						cli->reliable_session_id);
		return;
	}

	execute = !!strtol(argv[1], &endptr, 0);
	if (!endptr || *endptr != '\0') {
		LOG("Invalid execute: %s\n", argv[1]);
		return;
	}

	if (execute) {
		if (!bt_gatt_client_write_execute(cli->gatt, session_id,
							write_cb, NULL, NULL))
			LOG("Failed to proceed write execute\n");
	} else {
		bt_gatt_client_cancel(cli->gatt, session_id);
	}

	cli->reliable_session_id = 0;
}

/**
 * register notify usage
 */
static void register_notify_usage(void)
{
	LOG("Usage: register-notify <chrc value handle>\n");
}

/**
 * notify call back
 *
 * @param value_handle	handle of the notifying object
 * @param value			vector value of the object
 * @param length		length of vector value
 * @param user_data		not used
 */
int j = 0;
int start_header = 0;
uint8_t data[5] = {0};
uint8_t last_data[5] = {0};

int k = 0;
int start_header1 = 0;
uint8_t data1[17] = {0};
static void notify_cb(uint16_t value_handle, const uint8_t *value,
					uint16_t length, void *user_data)
{
	int i;

	LOG("\n\tHandle Value Not/Ind: 0x%04x - ", value_handle);

	if (length == 0) {
		PRLOG("(0 bytes)\n");
		return;
	}

	LOG("buf %s (%u bytes): ", buf, length);

	for (i = 0; i < length; i++)
		LOG("%02x ", value[i]);

	//PRLOG("\n");
        LOG("\n");

        if (value_handle == 0x35) {
                for (i = 0; i < length; i++) {
                        //LOG("%02x %02x %02x %02x %02x\n", data[0], data[1], data[2], data[3], data[4]);
                        if (value[i] == 0x80)  {/* find the start header */
                                start_header = 1;
                                j = 0;
                                data[j++] = value[i];
                        }
                        if (start_header == 1 && j <= 4 && j > 0 && value[i] != 0x80) {
                                data[j++] = value[i];
                        }
                        if (start_header == 1 && j == 5) {
                                LOG(" data      %02x %02x %02x %02x %02x\n", data[0], data[1], data[2], data[3], data[4]);
                                LOG(" last data %02x %02x %02x %02x %02x\n", last_data[0], last_data[1], last_data[2], last_data[3], last_data[4]);

                                if (memcmp(last_data+3, data+3, 2) != 0 &&
                                    (data[3] >=10 && data[3] <= 100) &&
                                    (data[4] >=10 && data[4] <= 100)) {
                                        uint8_t value[128] =  {0};
                                        int cfd = create_client_sock(CLIENT);
                                        snprintf(value, 127, "%s DATA %d;%d",
                                                 buf+8, data[3], data[4]);
                                        sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                                        close(cfd);
                                }

                                start_header = 0;
                                j = 0;
                                memcpy(last_data, data, 5);
                                memset(data, 0, 5);
                        }
                        if (start_header == 0)
                                continue;
                }
        } else if (value_handle == 0x13) {
                  for (i = 0; i < length; i++) {
                        if (value[i] == 0x03)  {/* find the start header */
                                start_header1 = 1;
                                k = 0;
                                data1[k++] = value[i];
                        }
                        if (start_header1 == 1 && k <= 16 && k > 0 && value[i] != 0x03) {
                                data[k++] = value[i];
                        }
                        if (start_header1 == 1 && k == 17) {
                                LOG(" data      %02x %02x %02x %02x %02x %02x %02x\n", data1[0], data1[1], data1[2], data1[3], data1[4], data1[12], data1[13]);
                                uint8_t value[128] =  {0};
                                int cfd = create_client_sock(CLIENT);
                                snprintf(value, 127, "%s DATA %d;%d",
                                         buf+8, data1[12], data1[13]);
                                sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                                close(cfd);

                                start_header1 = 0;
                                k = 0;
                                memset(data1, 0, 17);
                        }
                        if (start_header1 == 0)
                                continue;
                }
        }
}

/**
 *  register notify call back
 *
 * @param att_ecode		att error code
 * @param user_data		not used
 */
static void register_notify_cb(uint16_t att_ecode, void *user_data)
{
        uint8_t value[128] =  {0};
	if (att_ecode) {
		PRLOG("Failed to register notify handler "
					"- error code: 0x%02x\n", att_ecode);
                /* FIXME: XXX */
                /*
                unsigned int value1;
                rand_r(&value1);
                int cfd = create_client_sock(CLIENT);
                snprintf(value, 127, "%s DATA %.2f",
                         buf+8, (value1%60 + 40)/10.0);
                sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                close(cfd);
                */
		return;
	}

	PRLOG("Registered notify handler!");

        /* FIXME: XXX */
        /*
        unsigned int value1;
        rand_r(&value1);
        int cfd = create_client_sock(CLIENT);
        snprintf(value, 127, "%s DATA %.2f",
                 buf+8, (value1%60 + 40)/10.0);
        sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
        close(cfd);
        */
}

/**
 * register notify command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	register notify command string
 */
static void cmd_register_notify(struct client *cli, char *cmd_str)
{
	char *argv[2];
	int argc = 0;
	uint16_t value_handle;
	unsigned int id;
	char *endptr = NULL;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 1, argv, &argc) || argc != 1) {
		register_notify_usage();
		return;
	}

	value_handle = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !value_handle) {
		LOG("Invalid value handle: %s\n", argv[0]);
		return;
	}

	id = bt_gatt_client_register_notify(cli->gatt, value_handle,
							register_notify_cb,
							notify_cb, NULL, NULL);
	if (!id) {
		LOG("Failed to register notify handler\n");

                /* FIXME: XXX */
                /*
                if (match (cmd_str, "0x13")) {
                    uint8_t value[128] =  {0};
                    unsigned int value1;
                    rand_r(&value1);
                    int cfd = create_client_sock(CLIENT);
                    snprintf(value, 127, "%s DATA %.2f;",
                             buf+8, (value1%60 + 40)/10.0);
                    sock_send_cmd(cfd, SERVER, value, strlen(value)+1);
                    close(cfd);
                    return;
                }
                */
	}

	PRLOG("Registering notify handler with id: %u\n", id);
}

/**
 * un-register notify usage
 */
static void unregister_notify_usage(void)
{
	LOG("Usage: unregister-notify <notify id>\n");
}

/**
 * un-register notify command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	un-register notify command string
 */
static void cmd_unregister_notify(struct client *cli, char *cmd_str)
{
	char *argv[2];
	int argc = 0;
	unsigned int id;
	char *endptr = NULL;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 1, argv, &argc) || argc != 1) {
		unregister_notify_usage();
		return;
	}

	id = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || !id) {
		LOG("Invalid notify id: %s\n", argv[0]);
		return;
	}

	if (!bt_gatt_client_unregister_notify(cli->gatt, id)) {
		LOG("Failed to unregister notify handler with id: %u\n", id);
		return;
	}

	LOG("Unregistered notify handler with id: %u\n", id);
}

/**
 * set security usage
 */
static void set_security_usage(void)
{
	LOG("Usage: set_security <level>\n"
		"level: 1-3\n"
		"e.g.:\n"
		"\tset-sec-level 2\n");
}

/**
 * set security command
 *
 * @param cli		pointer to the client structure
 * @param cmd_str	set security command string
 */
static void cmd_set_security(struct client *cli, char *cmd_str)
{
	char *argvbuf[1];
	char **argv = argvbuf;
	int argc = 0;
	char *endptr = NULL;
	int level;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	if (!parse_args(cmd_str, 1, argv, &argc)) {
		LOG("Too many arguments\n");
		set_security_usage();
		return;
	}

	if (argc < 1) {
		set_security_usage();
		return;
	}

	level = strtol(argv[0], &endptr, 0);
	if (!endptr || *endptr != '\0' || level < 1 || level > 3) {
		LOG("Invalid level: %s\n", argv[0]);
		return;
	}

	if (!bt_gatt_client_set_security(cli->gatt, level))
		LOG("Could not set sec level\n");
	else
		LOG("Setting security level %d success\n", level);
}

/**
 * get security command
 *
 * @param cli		pointer to the client stricture
 * @param cmd_str	get security command string
 */
static void cmd_get_security(struct client *cli, char *cmd_str)
{
	int level;

	if (!bt_gatt_client_is_ready(cli->gatt)) {
		LOG("GATT client not initialized\n");
		return;
	}

	level = bt_gatt_client_get_security(cli->gatt);
	if (level < 0)
		LOG("Could not set sec level\n");
	else
		LOG("Security level: %u\n", level);
}

/**
 * convert sign key ascii to vector
 *
 * @param optarg	ascii key string
 * @param key		returned parsed vector
 * @return 			true if success else false
 */
static bool convert_sign_key(char *optarg, uint8_t key[16])
{
	int i;

	if (strlen(optarg) != 32) {
		LOG("sign-key length is invalid\n");
		return false;
	}

	for (i = 0; i < 16; i++) {
		if (sscanf(optarg + (i * 2), "%2hhx", &key[i]) != 1)
			return false;
	}

	return true;
}

/**
 * sign key usage
 */
static void set_sign_key_usage(void)
{
	LOG("Usage: set-sign-key [options]\nOptions:\n"
		"\t -c, --sign-key <csrk>\tCSRK\n"
		"e.g.:\n"
		"\tset-sign-key -c D8515948451FEA320DC05A2E88308188\n");
}

/**
 * counter increment sign_cnt by one
 *
 * @param sign_cnt		variable to increment
 * @param user_data		not used
 * @return				true
 */
static bool local_counter(uint32_t *sign_cnt, void *user_data)
{
	static uint32_t cnt = 0;

	*sign_cnt = cnt++;

	return true;
}

/**
 * set sign key command
 *
 * @param cli		pointer to client structure
 * @param cmd_str	set sign key command string
 */
static void cmd_set_sign_key(struct client *cli, char *cmd_str)
{
	char *argv[3];
	int argc = 0;
	uint8_t key[16];

	memset(key, 0, 16);

	if (!parse_args(cmd_str, 2, argv, &argc)) {
		set_sign_key_usage();
		return;
	}

	if (argc != 2) {
		set_sign_key_usage();
		return;
	}

	if (!strcmp(argv[0], "-c") || !strcmp(argv[0], "--sign-key")) {
		if (convert_sign_key(argv[1], key))
			bt_att_set_local_key(cli->att, key, local_counter, cli);
	} else
		set_sign_key_usage();
}

static void cmd_help(struct client *cli, char *cmd_str);

static void cmd_quit(struct client *cli, char *cmd_str){
	mainloop_quit();
}


typedef void (*command_func_t)(struct client *cli, char *cmd_str);

static struct {
	char *cmd;
	command_func_t func;
	char *doc;
} command[] = {
	{ "help", cmd_help, "\tDisplay help message" },
	{ "services", cmd_services, "\tShow discovered services" },
	{ "read-value", cmd_read_value,
				"\tRead a characteristic or descriptor value" },
	{ "read-long-value", cmd_read_long_value,
		"\tRead a long characteristic or desctriptor value" },
	{ "read-multiple", cmd_read_multiple, "\tRead Multiple" },
	{ "write-value", cmd_write_value,
			"\tWrite a characteristic or descriptor value" },
	{ "write-long-value", cmd_write_long_value,
			"Write long characteristic or descriptor value" },
	{ "write-prepare", cmd_write_prepare,
			"\tWrite prepare characteristic or descriptor value" },
	{ "write-execute", cmd_write_execute,
			"\tExecute already prepared write" },
	{ "register-notify", cmd_register_notify,
			"\tSubscribe to not/ind from a characteristic" },
	{ "unregister-notify", cmd_unregister_notify,
						"Unregister a not/ind session"},
	{ "set-security", cmd_set_security,
				"\tSet security level on le connection"},
	{ "get-security", cmd_get_security,
				"\tGet security level on le connection"},
	{ "set-sign-key", cmd_set_sign_key,
				"\tSet signing key for signed write command"},
	{ "quit", cmd_quit ,"\tQuit"},
	{ }
};

/**
 * help command
 *
 * @param cli		pointer to client structure
 * @param cmd_str	help command string
 */
static void cmd_help(struct client *cli, char *cmd_str)
{
	int i;

	LOG("Commands:\n");
	for (i = 0; command[i].cmd; i++)
		LOG("\t%-15s\t%s\n", command[i].cmd, command[i].doc);
}

/**
 * prompt read call back
 *
 * @param fd		stdin
 * @param events	epoll event
 * @param user_data pointer to client structure
 */
static void prompt_read_cb(int fd, uint32_t events, void *user_data)
{
        ssize_t numBytes;
        char buf[128];
        struct sockaddr_un claddr;
	//ssize_t read;
	socklen_t len = 0;
	char *line = NULL;
	char *cmd = NULL, *args;
	struct client *cli = user_data;
	int i;

	if (events & (EPOLLRDHUP | EPOLLHUP | EPOLLERR)) {
		mainloop_quit();
		return;
	}

        /*
	if ((read = getline(&line, &len, stdin)) == -1)
		return;

	if (read <= 1) {
		cmd_help(cli, NULL);
		print_prompt();
		return;
	}
        */
        len = sizeof(struct sockaddr_un);
        numBytes = recvfrom(fd, buf, 128, 0,
                            (struct sockaddr *) &claddr, &len);
        if (numBytes == -1)
                LOG("recvfrom error\n");

        LOG("[Client] received %ld bytes from %s\n", (long) numBytes,
               claddr.sun_path);

        LOG("[Client] C-> S : %s\n", buf);


	buf[numBytes] = '\0';
	args = buf;

	while ((cmd = strsep(&args, " \t")))
		if (*cmd != '\0')
			break;

	if (!cmd)
		goto failed;

	for (i = 0; command[i].cmd; i++) {
		if (strcmp(command[i].cmd, cmd) == 0)
			break;
	}

	if (command[i].cmd)
		command[i].func(cli, args);
	else
		fprintf(stderr, "Unknown command: %s\n", line);

failed:
	//print_prompt();

	free(line);
}

/**
 * signal call back SIGINT and SIGTERM processing
 *
 * @param signum		SIGXXX
 * @param user_data		unused
 */
static void signal_cb(int signum, void *user_data)
{
	switch (signum) {
	case SIGINT:
	case SIGTERM:
		mainloop_quit();
		break;
	default:
		break;
	}
}

/**
 * create a bluetooth le l2cap socket and connect src to dst
 *
 * @param src	6 bytes BD Address source address
 * @param dst	6 bytes BD Address destination address
 * @param dst_type  destination type BDADDR_LE_PUBLIC or BDADDR_LE_RANDOM
 * @param sec   security level BT_SECURITY_LOW or BT_SECURITY_MEDIUM or BT_SECURITY_HIGH
 * @return socket or -1 if error
 */
static int l2cap_le_att_connect(bdaddr_t *src, bdaddr_t *dst, uint8_t dst_type,
									int sec)
{
	int sock;
	struct sockaddr_l2 srcaddr, dstaddr;
	struct bt_security btsec;

	if (verbose) {
		char srcaddr_str[18], dstaddr_str[18];

		ba2str(src, srcaddr_str);
		ba2str(dst, dstaddr_str);

		LOG("btgatt-client: Opening L2CAP LE connection on ATT "
					"channel:\n\t src: %s\n\tdest: %s\n",
					srcaddr_str, dstaddr_str);
	}

	sock = socket(PF_BLUETOOTH, SOCK_SEQPACKET, BTPROTO_L2CAP);
	if (sock < 0) {
		perror("Failed to create L2CAP socket");
		return -1;
	}

	/* Set up source address */
	memset(&srcaddr, 0, sizeof(srcaddr));
	srcaddr.l2_family = AF_BLUETOOTH;
	srcaddr.l2_cid = htobs(ATT_CID);
	srcaddr.l2_bdaddr_type = 0;
	bacpy(&srcaddr.l2_bdaddr, src);

	if (bind(sock, (struct sockaddr *)&srcaddr, sizeof(srcaddr)) < 0) {
		perror("Failed to bind L2CAP socket");
		close(sock);
		return -1;
	}

	/* Set the security level */
	memset(&btsec, 0, sizeof(btsec));
	btsec.level = sec;
	if (setsockopt(sock, SOL_BLUETOOTH, BT_SECURITY, &btsec,
							sizeof(btsec)) != 0) {
		fprintf(stderr, "Failed to set L2CAP security level\n");
		close(sock);
		return -1;
	}

	/* Set up destination address */
	memset(&dstaddr, 0, sizeof(dstaddr));
	dstaddr.l2_family = AF_BLUETOOTH;
	dstaddr.l2_cid = htobs(ATT_CID);
	dstaddr.l2_bdaddr_type = dst_type;
	bacpy(&dstaddr.l2_bdaddr, dst);

	LOG("Connecting to device...");
	fflush(stdout);

	if (connect(sock, (struct sockaddr *) &dstaddr, sizeof(dstaddr)) < 0) {
		perror(" Failed to connect");
		close(sock);
		return -1;
	}

	printf(" Done\n");

	return sock;
}

/**
 * print usage
 */
static void usage(void)
{
	printf("btgatt-client\n");
	printf("Usage:\n\tbtgatt-client [options]\n");

	printf("Options:\n"
		"\t-i, --index <id>\t\tSpecify adapter index, e.g. hci0\n"
		"\t-d, --dest <addr>\t\tSpecify the destination address\n"
		"\t-t, --type [random|public] \tSpecify the LE address type\n"
		"\t-m, --mtu <mtu> \t\tThe ATT MTU to use\n"
		"\t-s, --security-level <sec> \tSet security level (low|"
								"medium|high)\n"
		"\t-v, --verbose\t\t\tEnable extra logging\n"
		"\t-h, --help\t\t\tDisplay help\n");

	printf("Example:\n"
			"btgattclient -v -d C4:BE:84:70:29:04\n");
}

static struct option main_options[] = {
	{ "index",		1, 0, 'i' },
	{ "dest",		1, 0, 'd' },
	{ "type",		1, 0, 't' },
	{ "mtu",		1, 0, 'm' },
	{ "security-level",	1, 0, 's' },
	{ "verbose",		0, 0, 'v' },
	{ "help",		0, 0, 'h' },
	{ }
};

/**
 * gatt client which browse ble device services and characteristics
 * @see usage function for args definition
 *
 * @param argc	args count
 * @param argv	args value
 * @return EXIT_FAILURE or EXIT_SUCCESS
 */
#if 0
int main(int argc, char *argv[])
{
	int opt;
	int sec = BT_SECURITY_LOW;
	uint16_t mtu = 0;
	uint8_t dst_type = BDADDR_LE_PUBLIC;
	bool dst_addr_given = false;
	bdaddr_t src_addr, dst_addr;
	int dev_id = -1;
	int fd;
	sigset_t mask;
	struct client *cli;

	while ((opt = getopt_long(argc, argv, "+hvs:m:t:d:i:",
						main_options, NULL)) != -1) {
		switch (opt) {
		case 'h':
			usage();
			return EXIT_SUCCESS;
		case 'v':
			verbose = true;
			break;
		case 's':
			if (strcmp(optarg, "low") == 0)
				sec = BT_SECURITY_LOW;
			else if (strcmp(optarg, "medium") == 0)
				sec = BT_SECURITY_MEDIUM;
			else if (strcmp(optarg, "high") == 0)
				sec = BT_SECURITY_HIGH;
			else {
				fprintf(stderr, "Invalid security level\n");
				return EXIT_FAILURE;
			}
			break;
		case 'm': {
			int arg;

			arg = atoi(optarg);
			if (arg <= 0) {
				fprintf(stderr, "Invalid MTU: %d\n", arg);
				return EXIT_FAILURE;
			}

			if (arg > UINT16_MAX) {
				fprintf(stderr, "MTU too large: %d\n", arg);
				return EXIT_FAILURE;
			}

			mtu = (uint16_t)arg;
			break;
		}
		case 't':
			if (strcmp(optarg, "random") == 0)
				dst_type = BDADDR_LE_RANDOM;
			else if (strcmp(optarg, "public") == 0)
				dst_type = BDADDR_LE_PUBLIC;
			else {
				fprintf(stderr,
					"Allowed types: random, public\n");
				return EXIT_FAILURE;
			}
			break;
		case 'd':
			if (str2ba(optarg, &dst_addr) < 0) {
				fprintf(stderr, "Invalid remote address: %s\n",
									optarg);
				return EXIT_FAILURE;
			}

			dst_addr_given = true;
			break;

		case 'i':
			dev_id = hci_devid(optarg);
			if (dev_id < 0) {
				perror("Invalid adapter");
				return EXIT_FAILURE;
			}

			break;
		default:
			fprintf(stderr, "Invalid option: %c\n", opt);
			return EXIT_FAILURE;
		}
	}

	if (!argc) {
		usage();
		return EXIT_SUCCESS;
	}

	argc -= optind;
	argv += optind;
	optind = 0;

	if (argc) {
		usage();
		return EXIT_SUCCESS;
	}

	if (dev_id == -1)
		bacpy(&src_addr, BDADDR_ANY);
	else if (hci_devba(dev_id, &src_addr) < 0) {
		perror("Adapter not available");
		return EXIT_FAILURE;
	}

	if (!dst_addr_given) {
		fprintf(stderr, "Destination address required!\n");
		return EXIT_FAILURE;
	}

	/* create the mainloop resources */
	mainloop_init();

	fd = l2cap_le_att_connect(&src_addr, &dst_addr, dst_type, sec);
	if (fd < 0)
		return EXIT_FAILURE;

	cli = client_create(fd, mtu);
	if (!cli) {
		close(fd);
		return EXIT_FAILURE;
	}

	/* add input event from console */
	if (mainloop_add_fd(fileno(stdin),
				EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR,
				prompt_read_cb, cli, NULL) < 0) {
		fprintf(stderr, "Failed to initialize console\n");
		return EXIT_FAILURE;
	}

	sigemptyset(&mask);
	sigaddset(&mask, SIGINT);
	sigaddset(&mask, SIGTERM);

	/* add handler for process interrupted (SIGINT) or terminated (SIGTERM)*/
	mainloop_set_signal(&mask, signal_cb, NULL, NULL);

	print_prompt();

	/* epoll main loop call
	 *
	 * any further process is an epoll event processed in mainloop_run
	 *
	 */
	mainloop_run();

	printf("\n\nShutting down...\n");

	client_destroy(cli);

	return EXIT_SUCCESS;
}

#endif


static void child_handler(int sig)
{
        pid_t pid;
        int status;

        while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {
                /* close the process */
                char cmd[128] = {0};
                /*
                snprintf(cmd, 127, "%s CLOSEID %d\n", buf+8, pid);
                int cfd = create_client_sock(CLIENT);
                sock_send_cmd(cfd, SERVER, cmd, strlen(cmd));
                printf("Close PID %d\n", pid);
                close(cfd);
                */
                snprintf(cmd, 127, "CLOSEID %d", pid);
                int cfd = create_client_sock(CLIENT);
                sock_send_cmd(cfd, SERVER, cmd, strlen(cmd)+1);
                LOG("Close PID %d\n", pid);
                close(cfd);
        }
}

char cmd1[] = {0xcc, 0x96, 0x02, 0x03, 0x01, 0x01, 0x00, 0x01};
char cmd2[] = {0xcc, 0x96, 0x02, 0x03, 0x01, 0x02, 0x00, 0x02};

int
main(int argc, char *argv[])
{
        struct sockaddr_un svaddr, claddr;
        int sfd;
        ssize_t numBytes;
        socklen_t len;

        struct sigaction sa;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sa.sa_handler = child_handler;

        sigaction(SIGCHLD, &sa, NULL);

        srand(time(NULL));

        sfd = socket(AF_UNIX, SOCK_DGRAM, 0);       /* Create server socket */
        if (sfd == -1)
                LOG("socket create error.\n");

        /* Construct well-known address and bind server socket to it */

        /* For an explanation of the following check, see the erratum note for
           page 1168 at http://www.man7.org/tlpi/errata/. */
        if (remove(CLIENT) == -1 && errno != ENOENT)
                LOG("remove-%s error.\n", CLIENT);

        memset(&svaddr, 0, sizeof(struct sockaddr_un));
        svaddr.sun_family = AF_UNIX;
        strncpy(svaddr.sun_path, CLIENT, sizeof(svaddr.sun_path) - 1);

        if (bind(sfd, (struct sockaddr *) &svaddr, sizeof(struct sockaddr_un)) == -1)
                LOG("bind error.\n");

        /* Receive messages */
        for (;;) {
        retry:
                len = sizeof(struct sockaddr_un);
                memset(buf, 0, BUF_SIZE);
                numBytes = recvfrom(sfd, buf, BUF_SIZE, 0,
                                    (struct sockaddr *) &claddr, &len);
                if (numBytes == -1) {
                        LOG("recvfrom error, will retry \n");
                        usleep(500000);
                        goto retry;
                }

                /*
                printf("Server received %ld bytes from %s : %s\n", (long) numBytes,
                       claddr.sun_path, buf);
                */
                /* create child process */
                pid_t pid = fork();
                switch(pid) {
                case -1:
                        LOG("Create process error %s\n", buf);
                        break;
                case 0:
                {
                        int cfd = create_client_sock(CLIENT);
                        /* create process sucess */
                        LOG("in child process %s pid %d\n", buf, getpid());

                        char cmd[128] = {0};
                        snprintf(cmd, 127, "%s PROCESS %d", buf+8, getpid());
                        sock_send_cmd(cfd, SERVER, cmd, strlen(cmd)+1);

                        if (strstr(buf, "type")) {
                                struct sockaddr_rc loc_addr = { 0 };
                                char address[18] = {0};
                                bdaddr_t dst_addr;
                                int s;
                                int status;
                                memcpy(address, buf+8, 17);
                                if (str2ba(address, &dst_addr) < 0) {
                                        LOG("Invalid remote address: %s\n", address);
                                        return EXIT_FAILURE;
                                }
                                s = socket(AF_BLUETOOTH, SOCK_STREAM, BTPROTO_RFCOMM);
                                loc_addr.rc_family = AF_BLUETOOTH;
                                loc_addr.rc_channel = 6;
				//loc_addr.rc_bdaddr = *(&(info+i)->bdaddr);
                                bacpy(&loc_addr.rc_bdaddr, &dst_addr);
				status = connect(s, (struct sockaddr *)&loc_addr, sizeof(loc_addr));
				if (status < 0) {
                                        snprintf(cmd, 127, "%s DISCONN fail", buf+8);
                                        sock_send_cmd(cfd, SERVER, cmd, strlen(cmd)+1);
                                        return EXIT_FAILURE;
                                }

                                status = write(s, cmd1, 8);
				usleep(100);
				status = write(s, cmd2, 8);
				LOG ("Wrote %d bytes [CMD to RPB]\n", status);

				uint8_t buf[128];
				ssize_t len;
				do {
					len = read(s, buf, 128);
                                        if (len == 20) {
                                                LOG("read %d bytes\n", len);
                                                hexdump(buf, len);
                                                /*
                                                                                                 Sys  Dia  Pulse
                                                  AA96020F 0106000E 01010101 0100A600 75004F99   22.1 15.6 79
                                                  AA96020F 0106000E 01010101 0100A700 82005474   22.2 17.3 84
                                                  AA96020F 0106000E 01010101 0100A300 72005084   21.7 15.2 80
                                                  AA96020F 0106000E 01010101 0100AD00 9100566F   23.0 19.3 86
                                                  AA960203 01070205                              ERROR

                                                  Pulse buf[18] Sys buf[14]                 Dia buf[16]
                                                  4F => 79     A6(166) => x 4 / 30  = 22.1  75(117) => x 2 / 15 = 15.6
                                                  54 => 84     A7(167) => x 4 / 30  = 22.2  82(130) => x 2 / 15 = 17.3
                                                  50 => 80     A3(163) => x 4 / 30  = 21.7  72(114) => x 2 / 15 = 15.2
                                                  56 => 86     AD(173) => x 4 / 30  = 23.0  91(145) => x 2 / 15 = 19.3
                                                */
                                                uint8_t data[128] =  {0};
                                                snprintf(data, 127, "%s DATA %d;%.1f;%.1f",
                                                         address, buf[18], (buf[14] * 4)/30.0, (buf[16] * 2)/15.0);
                                                sock_send_cmd(cfd, SERVER, data, strlen(data)+1);
                                                sleep(60);
                                                close(s);
                                                return;
                                        } else if (len > 0){
                                                hexdump(buf, len);
                                        }
				} while (len > 0);
                                sleep(60);
                                close(s);
                                return;

                        } else if (strstr(buf, "sniffer")) {
                                sniffer(argv[1]);
                                //sniffer("wlp1s0");
                        } else {
                                int sec = BT_SECURITY_LOW;
                                uint16_t mtu = 0;
                                uint8_t dst_type = BDADDR_LE_PUBLIC;
                                bdaddr_t src_addr, dst_addr;
                                int fd;
                                struct client *cli;
                                char address[18] = {0};
                                memcpy(address, buf+8, 17);
                                if (str2ba(address, &dst_addr) < 0) {
                                        fprintf(stderr, "Invalid remote address: %s\n",
									address);
                                        return EXIT_FAILURE;
                                }

                                bacpy(&src_addr, BDADDR_ANY);

                                /* create the mainloop resources */
                                mainloop_init();

                                fd = l2cap_le_att_connect(&src_addr, &dst_addr, dst_type, sec);
                                if (fd < 0) {
                                        snprintf(cmd, 127, "%s DISCONN fail >>>>>>>>", buf+8);
                                        sock_send_cmd(cfd, SERVER, cmd, strlen(cmd)+1);
                                        return EXIT_FAILURE;
                                }

                                cli = client_create(fd, mtu);
                                if (!cli) {
                                        close(fd);
                                        snprintf(cmd, 127, "%s DISCONN fail ========= ", buf+8);
                                        sock_send_cmd(cfd, SERVER, cmd, strlen(cmd)+1);
                                        return EXIT_FAILURE;
                                }

                                /*
                                snprintf(cmd, 127, "%s CONNECT sucess\n", buf+8);
                                sock_send_cmd(cfd, SERVER, cmd, strlen(cmd));
                                */

                                /* add input event from console */
                                if (mainloop_add_fd(cfd,
                                                    EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR,
                                                    prompt_read_cb, cli, NULL) < 0) {
                                        fprintf(stderr, "Failed to initialize client server\n");
                                        return EXIT_FAILURE;
                                }

                                /* add handler for process interrupted (SIGINT) or terminated (SIGTERM)*/
                                //mainloop_set_signal(&mask, signal_cb, NULL, NULL);


                                /* epoll main loop call
                                 *
                                 * any further process is an epoll event processed in mainloop_run
                                 *
                                 */
                                mainloop_run();

                                printf("\n\nShutting down...\n");

                                client_destroy(cli);

                                return 0;
                        }
                }
                        break;
                default:
                        /* Do nothing */
                        break;
                }
        }
}
