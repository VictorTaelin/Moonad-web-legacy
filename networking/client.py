import sys, time, signal, asyncore, socket

def sendHello(signum, frame):
    print "Alarm handler"
    sent = udp.sendto("hello", address) #TODO: define 'address'
    signal.alarm(5)


HOST = '127.0.0.1'  # Default IP Address
PORT = 0

MESSAGE = "Hello!"

# Read arguments
argc = len(sys.argv)
if ((argc < 2) or (argc > 3)):
    # Incorrect usage
    print "Usage: python client.py [IP_ADDR] PORT"
    print "If no IP Address is provided, it will default to 127.0.0.1"
    sys.exit()
elif (argc == 2):
    # Only PORT was provided. Use default IP address
    PORT = int(sys.argv[1])
else:
    # Both IP Address and PORT provided
    HOST = sys.argv[1]
    PORT = sys.argv[2]

# Setup Alarm
signal.signal(signal.SIGALRM, sendHello)
signal.alarm(5)

#######################################
# Initiate UDP communication
udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

# Bind the socket to the port
addr = (HOST, PORT)
udp.bind(addr)

while True:
    print('\nwaiting to receive message')
    data, address = udp.recvfrom(4096)

    print('received {} bytes from {}'.format(
        len(data), address))
    print(data)

    if data:
        sent = udp.sendto(data, address)
        print('sent {} bytes back to {}'.format(
            sent, address))
