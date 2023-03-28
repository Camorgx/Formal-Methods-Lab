from a_plus_b import plus, formal


def to_binary(a: int, b: int):
    if a < b:
        a, b = b, a
    a = bin(a)[2:]
    b = bin(b)[2:]
    n = len(a)
    if len(b) < n:
        b = (n - len(b)) * '0' + b
    b = ''.join('0' if bit == '1' else '1' for bit in b)
    return n, a, b


def minus(a: int, b: int) -> int:
    n, str_a, str_b = to_binary(a, b)
    return plus(formal(n, str_a, str_b, True), 1)


def main():
    a, b = map(int, input('Input a and b in one line: ').split())
    print(f'|{a} - {b}| = {minus(a, b)}')


if __name__ == '__main__':
    main()
