#define	arrsize 64

unsigned long volatile A[arrsize];
unsigned long volatile B[arrsize];
unsigned int secret;

int main() {
        unsigned int temp;
	unsigned int i;

        for (i = 0; i < arrsize; i++)
        	temp = A[i];

        if (secret < arrsize)
		temp = B[secret];
}
