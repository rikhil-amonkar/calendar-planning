import sys
sys.setrecursionlimit(20000)

travel_times = {
    'A': {'B': 1, 'C': 1, 'D': 1, 'E': 2, 'F': 2, 'G': 2},
    'B': {'A': 1, 'C': 2, 'D': 2, 'E': 1, 'F': 2, 'G': 2},
    'C': {'A': 1, 'B': 2, 'D': 1, 'E': 2, 'F': 1, 'G': 2},
    'D': {'A': 1, 'B': 2, 'C': 1, 'E': 2, 'F': 2, 'G': 1},
    'E': {'A': 2, 'B': 1, 'C': 2, 'D': 2, 'F': 1, 'G': 1},
    'F': {'A': 2, 'B': 2, 'C': 1, 'D': 2, 'E': 1, 'G': 1},
    'G': {'A': 2, 'B': 2, 'C': 2, 'D': 1, 'E': 1, 'F': 1}
}

all_cities = set("ABCDEFG")
memo = {}

def dfs(current_city, current_start_day, visited):
    key = (current_city, current_start_day, visited)
    if key in memo:
        return memo[key]
    
    for s in range(1, 25 - current_start_day + 1):
        end_day = current_start_day + s - 1
        if end_day > 24:
            break
        new_visited = visited | {current_city}
        
        if end_day == 24:
            if current_city == 'A' and new_visited == all_cities:
                seg = [(current_city, current_start_day, end_day)]
                memo[key] = seg
                return seg
            else:
                continue
        
        for next_city in all_cities:
            if next_city == current_city:
                continue
            travel_time = travel_times[current_city][next_city]
            arrival_day = end_day + travel_time
            if arrival_day > 24:
                continue
            next_segment = dfs(next_city, arrival_day, frozenset(new_visited))
            if next_segment is not None:
                full_segment = [(current_city, current_start_day, end_day)] + next_segment
                memo[key] = full_segment
                return full_segment
    
    memo[key] = None
    return None

result = dfs('A', 1, frozenset())
if result is None:
    print("No solution found")
else:
    for segment in result:
        print(f"{segment[0]}{segment[1]}{segment[2]}", end=" ")
    print()