def find_median(arr):
    if len(arr) == 0:
        return None
    sorted_arr = sorted(arr)
    n = len(sorted_arr)
    if n % 2 == 1:
        return sorted_arr[n//2]
    else:
        return (sorted_arr[n//2 - 1] + sorted_arr[n//2]) / 2.0

if __name__ == '__main__':
    print(find_median([]))         # None
    print(find_median([5]))        # 5
    print(find_median([5, 2]))     # 3.5
    print(find_median([3, 1, 2]))  # 2