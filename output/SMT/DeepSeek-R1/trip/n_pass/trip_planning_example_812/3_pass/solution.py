from collections import deque

graph = {
    0: [1, 2],
    1: [0, 2, 3, 4],
    2: [0, 1, 3],
    3: [1, 2, 4],
    4: [1, 3, 5],
    5: [4]
}

def main():
    memo = set()
    queue = deque()
    starts = [1, 2]  # B and C
    mapping = {0: 'A', 1: 'B', 2: 'C', 3: 'D', 4: 'E', 5: 'F'}
    for start in starts:
        freqs = [0] * 5
        idx = start - 1
        freqs[idx] = 1
        state = (start, 1, tuple(freqs))
        memo.add(state)
        queue.append((start, 1, tuple(freqs), [start]))
    
    found_path = None
    while queue:
        current, length, freqs, path = queue.popleft()
        
        if length < 19:
            missing = 0
            for count in freqs:
                if count == 1:
                    missing += 1
            if missing > (19 - length):
                continue
                
        if length == 19:
            if current in [1, 2]:
                valid = True
                for count in freqs:
                    if count == 1:
                        valid = False
                        break
                if valid:
                    found_path = path
                    break
        else:
            for neighbor in graph[current]:
                if neighbor == 0:
                    continue
                lst = list(freqs)
                idx = neighbor - 1
                lst[idx] += 1
                new_freqs = tuple(lst)
                new_state = (neighbor, length + 1, new_freqs)
                if new_state not in memo:
                    memo.add(new_state)
                    new_path = path + [neighbor]
                    queue.append((neighbor, length + 1, new_freqs, new_path))
    
    if found_path is not None:
        full_path = [0] + found_path + [0]
        result = [mapping[x] for x in full_path]
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()