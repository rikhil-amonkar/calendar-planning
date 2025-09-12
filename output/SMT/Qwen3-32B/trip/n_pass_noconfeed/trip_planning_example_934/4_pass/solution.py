durations = [10, 20, 30, 40, 50, 60, 70, 80]
perm = [0, 2, 5, 7]  # Example permutation of indices

for j in range(len(perm)):
    value = durations[perm[j]] if perm[j] < 7 else 0
    print(f"Index {perm[j]}: Duration = {value}")