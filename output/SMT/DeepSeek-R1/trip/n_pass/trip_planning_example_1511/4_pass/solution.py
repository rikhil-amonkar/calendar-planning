import sys
sys.setrecursionlimit(30000)

travel_times = {
    'A': {'B': 1, 'C': 1, 'D': 1, 'E': 2, 'F': 2, 'G': 2},
    'B': {'A': 1, 'C': 2, 'D': 2, 'E': 1, 'F': 2, 'G': 2},
    'C': {'A': 1, 'B': 2, 'D': 1, 'E': 2, 'F': 1, 'G': 2},
    'D': {'A': 1, 'B': 2, 'C': 1, 'E': 2, 'F': 2, 'G': 1},
    'E': {'A': 2, 'B': 1, 'C': 2, 'D': 2, 'F': 1, 'G': 1},
    'F': {'A': 2, 'B': 2, 'C': 1, 'D': 2, 'E': 1, 'G': 1},
    'G': {'A': 2, 'B': 2, 'C': 2, 'D': 1, 'E': 1, 'F': 1}
}

all_cities = frozenset("ABCDEFG")
memo = {}

def dfs(current_city, current_end_day, visited):
    key = (current_city, current_end_day, visited)
    if key in memo:
        return memo[key]
    
    if visited == all_cities:
        if current_city == 'A':
            if current_end_day == 24:
                memo[key] = []
                return []
            else:
                memo[key] = None
                return None
        else:
            t = travel_times[current_city]['A']
            next_start = current_end_day + t + 1
            if next_start > 24:
                memo[key] = None
                return None
            duration = 24 - next_start + 1
            if duration < 1:
                memo[key] = None
                return None
            segment = [('A', next_start, 24)]
            memo[key] = segment
            return segment

    for next_city in all_cities:
        if next_city == current_city:
            continue
        t = travel_times[current_city][next_city]
        next_start = current_end_day + t + 1
        if next_start > 24:
            continue
        max_duration = 24 - next_start + 1
        for d in range(1, max_duration + 1):
            next_end = next_start + d - 1
            new_visited = visited | {next_city}
            next_segments = dfs(next_city, next_end, new_visited)
            if next_segments is not None:
                seg = [(next_city, next_start, next_end)] + next_segments
                memo[key] = seg
                return seg
    memo[key] = None
    return None

def main():
    for d0 in range(1, 25):
        end0 = d0
        visited0 = frozenset({'A'})
        if end0 == 24:
            if visited0 == all_cities:
                return [('A', 1, 24)]
            else:
                continue
        segments_after = dfs('A', end0, visited0)
        if segments_after is not None:
            return [('A', 1, end0)] + segments_after
    return None

itinerary = main()
if itinerary is None:
    print("No solution found")
else:
    output = ""
    for seg in itinerary:
        city, start, end = seg
        output += f"{city}{start}{end}"
    print(output)