#include <stdio.h>
#include <stdlib.h>
#include <strings.h>

#define MD5_CBLOCK      64
#define MD5_LBLOCK      (MD5_CBLOCK/4)
#define MD5_DIGEST_LENGTH 16
#define MD5_LONG unsigned long
typedef struct MD5state_st {
	MD5_LONG	A     , B, C, D;
	MD5_LONG	Nl    , Nh;
	MD5_LONG	data   [MD5_LBLOCK];
	unsigned int	num;
}		MD5_CTX;

int
		MD5_Init      (MD5_CTX * c);
int		MD5_Update (MD5_CTX * c, const void *data, size_t len);
int		MD5_Final  (unsigned char *md, MD5_CTX * c);
unsigned char  *MD5(const unsigned char *d, size_t n, unsigned char *md);

typedef void   *caddr_t;


void
hmac_md5(unsigned char *text /* pointer to data stream */ ,
	 int text_len /* length of data stream */ ,
	 unsigned char *key /* pointer to authentication key */ ,
	 int key_len /* length of authentication key */ ,
	 caddr_t digest /* caller digest to be filled in */ )
{
	MD5_CTX		context;
	unsigned char	k_ipad[65];	/* inner padding - key XORd with ipad */
	unsigned char	k_opad[65];	/* outer padding - key XORd with opad */
	unsigned char	tk[16];
	int		i;
	/* if key is longer than 64 bytes reset it to key=MD5(key) */
	if (key_len > 64) {

		MD5_CTX		tctx;

		MD5Init(&tctx);
		MD5Update(&tctx, key, key_len);
		MD5Final(tk, &tctx);

		key = tk;
		key_len = 16;
	}
	/*
	 * * the HMAC_MD5 transform looks like: *
	 * 
	 * MD5(K XOR opad, MD5(K XOR ipad, text)) *
	 * 
	 * where K is an n byte key * ipad is the byte 0x36 repeated 64 times
	 * 
	 * 
	 * 
	 * Krawczyk, et. al.            Informational                      [Page
	 * 8]
	 * 
	 * RFC 2104                          HMAC                     February
	 * 1997
	 * 
	 * 
	 * opad is the byte 0x5c repeated 64 times * and text is the data being
	 * protected
	 */

	/* start out by storing key in pads */
	bzero(k_ipad, sizeof k_ipad);
	bzero(k_opad, sizeof k_opad);
	bcopy(key, k_ipad, key_len);
	bcopy(key, k_opad, key_len);

	/* XOR key with ipad and opad values */
	for (i = 0; i < 64; i++) {
		k_ipad[i] ^= 0x5c;
		k_opad[i] ^= 0x36;
	}
	/*
	 * * perform inner MD5
	 */
	MD5Init(&context);	/* init context for 1st pass */
	MD5Update(&context, k_ipad, 64);	/* start with inner pad */
	MD5Update(&context, text, text_len);	/* then text of datagram */
	MD5Final(digest, &context);	/* finish up 1st pass */
	/*
	 * * perform outer MD5
	 */
	MD5Init(&context);	/* init context for 2nd pass */
	MD5Update(&context, k_opad, 64);	/* start with outer pad */
	MD5Update(&context, digest, 16);	/* then results of 1st hash */
	MD5Final(digest, &context);	/* finish up 2nd pass */
}


int main(int argc, char **argv) {
  unsigned char text[64];
  unsigned char key[64];
  unsigned char digest[160];
  hmac_md5(text, sizeof(text), key, sizeof(key), digest);
}
