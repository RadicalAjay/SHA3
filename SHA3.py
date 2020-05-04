#! usr/bin/env python3
# coding: UTF-8
# author: Ajay Dyavathi
# algorithm reference: 'https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf'



class SHA3():

    def __init__(self, output=224):
        ''' SHA3 class, choose output bit range from(224, 256, 384, 512)
            the state contains 1600 bits for standard SHA3
        '''
        rate = {224: 1152, 256: 1088, 384: 832, 512: 576}
        self.output = output
        assert self.output in rate, 'Invalid bit length'
        self.rate = rate[self.output]
        self.state_value = 1600
        self.capacity = self.state_value - self.rate
        self.bus = self.rate + self.capacity

    def __str__(self):
        return f'SHA3-{self.output}'


    def ascii2bin(self, asc):
        '''Convert ascii string to binary string'''
        return ''.join('{:08b}'.format(ord(char)) for char in asc)


    def bin2hex(self, bn):
        return ''.join('{:0x}'.format(int(bn[i:i+4], 2)) for i in range(0, len(bn), 4))


    def pad_with(self, x, m):
        '''pad m using pad10*1 algorithm such that m+pad is a positive multiple of x'''
        assert x > 0 and m >= 0
        # the pad should be surrounded by '1' with either sides,
        # 0* indicates number of zeros stuffed in between
        # hence, the name 10*1
        j = (-m - 2) % x
        pad = '1' + ('0' * j) + '1'
        return pad


    def preprocess(self, message):
        '''Pad the message and break it into chunks'''
        message = self.ascii2bin(message)
        padded_message = message + self.pad_with(self.rate, len(message))
        message_blocks = [padded_message[i:i + self.rate] for i in range(0, len(padded_message), self.rate)]
        return message_blocks


    def change_conventions(self, state):
        ''' every coordinate is added with 2 and modulo 5, because of labelling convention mentioned in
            documentation, (0, 0) should be the lan at center of state.'''
        state_ = [[['' for z in range(64)] for y in range(5)] for x in range(5)]

        for x in range(5):
            for y in range(5):
                state_[x][y] = list(self.lane(state, (x+2)%5, (y+2)%5))
        return state_

    def theta(self, state):
        '''1. For all pairs (x, z) such that 0≤x<5 and 0≤z<w, let
                C[x,z]=A[x,0,z] ⊕ A[x,1,z] ⊕ A[x,2,z] ⊕ A[x,3,z] ⊕ A[x,4,z].

            2. For all pairs (x, z) such that 0≤x<5 and 0≤z<w let
                D[x, z]=C[(x-1) mod 5, z] ⊕ C[(x+1) mod 5, (z–1) mod w].

            3. For all triples (x, y, z) such that 0≤x<5, 0≤y<5, and 0≤z<w, let
                A′[x,y,z] = A[x,y,z] ⊕ D[x,z].'''

        def C(x, z):
            return self.xor(*[state[x][i][z] for i in range(5)])

        def D(x, z):
            return self.xor_2( C((x-1) % 5, z), C((x+1) % 5, (z-1) % 64) )

        state_ = [[['' for z in range(64)] for y in range(5)] for x in range(5)]

        for x in range(5):
            for y in range(5):
                for z in range(64):
                    state_[x][y][z] = self.xor_2(state[x][y][z], D(x, z))
        return state_


    def rot(self, word, shift):
        ''' rotate the word right side with given shift,
            >>> rot('12345', 2) == '45123'
        '''
        shift = shift % len(word)
        return word[-shift:]+word[:-shift]

    def rho(self, state):
        ''' 1. For all z such that 0≤z<w, let A′ [0,0,z] = A[0,0,z].
            2. Let(x,y)=(1,0).
            3. For t from 0 to 23:
                    a. for all z such that 0≤z<w, let A′[x, y, z] = A[x, y, (z–(t+1)(t+2)/2) mod w];
                    b. let (x, y) = (y, (2x+3y) mod 5).
            4. Return A′.'''

        rot_vals = [[153, 231, 3, 10, 171],
                    [55, 276, 36, 300, 6],
                    [28, 91, 0, 1, 190],
                    [120, 78, 210, 66, 253],
                    [21, 136, 105, 45, 15]]

        state_ = [[['' for z in range(64)] for y in range(5)] for x in range(5)]

        for x in range(5):
            for y in range(5):
                state_[y][((2*x) + (3*y)) %5] = list(self.rot(self.lane(state, x, y), rot_vals[(y+2)%5][(x+2)%5]%64))

        return state_

    def pi(self, state):
        '''For all triples (x, y, z) such that 0≤x<5, 0≤y<5, and 0≤z<w, let
                A′[x, y, z]= A[(x + 3y) mod 5, x, z].'''
        state_ = [[['' for z in range(64)] for y in range(5)] for x in range(5)]
        for x in range(5):
            for y in range(5):
                for z in range(64):
                    state_[x][y][z] = state[(x+(3*y))%5][x][z]
        return state_


    def chi(self, state):
        '''A′[x,y,z] = A[x,y,z] ⊕ ((A[(x+1) mod 5, y, z] ⊕ 1) ⋅ A[(x+2) mod 5, y, z])'''
        state_ = [[['' for z in range(64)] for y in range(5)] for x in range(5)]

        for x in range(5):
            for y in range(5):
                state_[x][y] = list(self.xor_2(self.lane(state, x, y), bin((int(self.lane(state, (x+1)%5, y), 2) ^ 1) & int(self.lane(state, (x+2)%5, y), 2))[2:].zfill(64)))
        return state_

    def iota(self, state):
        RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
              0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
              0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
              0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
              0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
              0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,]

        state_ = [[['' for z in range(64)] for y in range(5)] for x in range(5)]
        for x in range(5):
            for y in range(5):
                state_[x][y] = list(self.xor_2(self.lane(state, x, y), bin(RC[self.round_count])[2:].zfill(64)))

        return state_


    def lane(self, state, x, y):
        '''return 1D lane at given (x, y) coordinate'''
        lane_ = ''.join(state[x][y])
        assert len(state[x][y]) == 64
        assert len(lane_) == 64, (x, y)
        return lane_


    def plane(self, state, y):
        '''return 2D plane at given y-location'''
        return ''.join(self.lane(state, i, y) for i in range(5))
        

    def form_state(self, data):
        '''Forms a cuboid matrix with dimensions 5x5x64'''

        # verify the length of data == 1600
        assert len(data) == 1600
        # create an empty state of 5x5x64 dimensions
        state = [[['' for z in range(64)] for y in range(5)] for x in range(5)]
        # replace the items of state with that of data
        for x in range(5):
            for y in range(5):
                for z in range(64):
                    state[x][y][z] = data[64 * ((5 * y) + x) + z]

        # verify that unpacked_state == data 
        assert data == ''.join(self.plane(state, i) for i in range(5))
        return self.change_conventions(state)


    def xor_2(self, a, b):
        '''Performs binary XOR operation of 2 words'''
        return ''.join('0' if i == j else '1' for i, j in zip(a, b))


    def xor(self, *words):
        '''Performs binary XOR operation of multiple words'''
        first, *words = words
        result = first
        for word in words:
            result = self.xor_2(result, word)

        return result

    def _round(self, b):
        '''Compute a single round on data "b" '''
        b = self.theta(b)
        b = self.rho(b)
        b = self.pi(b)
        b = self.chi(b)
        b = self.iota(b)
        return b


    def f(self, r, c):
        '''Compute 24 rounds'''
        b = r + c
        assert len(b) == 1600
        state = self.form_state(b)
        self.rounds = 24
        for i in range(self.rounds):
            self.round_count = i
            state = self._round(state)
        unpacked_state = ''.join(self.plane(state, i) for i in range(5))
        return unpacked_state[:self.rate], unpacked_state[self.rate:]

    def _hash(self, message):
        '''Computes SHA3 Hash'''
        message = self.preprocess(message)
        # intiial r, c are zero filled vectors
        r = '0' * self.rate
        c = '0' * self.capacity
        for block in message:
            # f input is previous r ⊕ message_block
            f_inp = self.xor_2(block, r)
            r, c = self.f(f_inp, c)

        # output is truncated MSBs of result at length of choosen bits
        value = r[:self.output]
        return self.bin2hex(value)


hash_this = 'SHA3 is incredible!'

sha = SHA3(224)
hashed = sha._hash(hash_this)
print(sha.__str__(), hashed)

sha = SHA3(256)
hashed = sha._hash(hash_this)
print(sha.__str__(), hashed)

sha = SHA3(384)
hashed = sha._hash(hash_this)
print(sha.__str__(), hashed)

sha = SHA3(512)
hashed = sha._hash(hash_this)
print(sha.__str__(), hashed)