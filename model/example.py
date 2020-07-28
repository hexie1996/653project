def foo():
    i = 0
    while True:
        i += 1
        if i == 3:
            break
    for j in range(3):
        i += j
        if j == 2:
            break
    return i

fib_gen = fib()
for _ in range(10):
    next(fib_gen)