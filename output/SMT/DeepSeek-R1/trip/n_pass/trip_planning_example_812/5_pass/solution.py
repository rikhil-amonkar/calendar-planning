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
    mapping = {0: 'A', 1: 'B', 2: 'C', 3: 'D', 4: 'E', 5: 'F'}
    visited = set()
    queue = deque()
    start_freqs = (0, 0, 0, 0, 0)
    start_state = (0, 0, 1, start_freqs, False)
    visited.add(start_state)
    queue.append((0, 0, 1, start_freqs, False, [0]))
    
    solution_path = None
    while queue:
        d, city, seg_len, freqs, fsd, path = queue.popleft()
        
        if d == 19:
            if city == 0 and freqs == (2, 2, 2, 2, 2):
                solution_path = [mapping[i] for i in path]
                break
            continue
        
        new_d = d + 1
        
        new_freqs_stay = freqs
        if city != 0:
            idx = city - 1
            count_val = freqs[idx]
            if count_val < 2:
                lst_freqs = list(freqs)
                lst_freqs[idx] = count_val + 1
                new_freqs_stay = tuple(lst_freqs)
        
        new_seg_len_stay = seg_len + 1
        new_fsd_stay = fsd
        new_state_stay = (new_d, city, new_seg_len_stay, new_freqs_stay, new_fsd_stay)
        if new_state_stay not in visited:
            visited.add(new_state_stay)
            new_path_stay = path + [city]
            queue.append((new_d, city, new_seg_len_stay, new_freqs_stay, new_fsd_stay, new_path_stay))
        
        if (city == 0 and not fsd) or (seg_len >= 2):
            for neighbor in graph[city]:
                if neighbor == city:
                    continue
                new_city = neighbor
                new_seg_len_move = 1
                new_freqs_move = freqs
                if neighbor != 0:
                    idx = neighbor - 1
                    count_val = freqs[idx]
                    if count_val < 2:
                        lst_freqs = list(freqs)
                        lst_freqs[idx] = count_val + 1
                        new_freqs_move = tuple(lst_freqs)
                new_fsd_move = fsd
                if city == 0 and not fsd:
                    new_fsd_move = True
                new_state_move = (new_d, new_city, new_seg_len_move, new_freqs_move, new_fsd_move)
                if new_state_move not in visited:
                    visited.add(new_state_move)
                    new_path_move = path + [neighbor]
                    queue.append((new_d, new_city, new_seg_len_move, new_freqs_move, new_fsd_move, new_path_move))
    
    if solution_path:
        print(solution_path)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()