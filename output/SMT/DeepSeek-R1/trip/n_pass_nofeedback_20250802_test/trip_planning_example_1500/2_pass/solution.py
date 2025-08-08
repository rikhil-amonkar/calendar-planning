mod = 1000000007
n = int(input().strip())
for _ in range(n-1):
    input()  # Skip the parent information for each node (from 1 to n-1)
print(pow(2, n-1, mod))