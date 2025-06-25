def find_median(arr):
    if not arr:
        return None
    arr_sorted = sorted(arr)
    n = len(arr)
    if n % 2 == 1:
        return arr_sorted[n//2]
    else:
        return (arr_sorted[n//2 - 1] + arr_sorted[n//2]) / 2