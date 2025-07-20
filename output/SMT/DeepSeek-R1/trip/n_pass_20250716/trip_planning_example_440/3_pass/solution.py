def main():
    forbidden_moves = {('Paris', 'Rome'), ('Rome', 'Paris'), ('London', 'Berlin'), ('Berlin', 'London')}
    cities = ['London', 'Paris', 'Rome', 'Berlin']
    
    def dfs(itinerary, visited):
        if len(itinerary) == 12:
            if itinerary[-1] != 'London' or set(visited) != set(cities):
                return None
            return itinerary
        
        current_city = itinerary[-1]
        for next_city in cities:
            if next_city != current_city:
                if (current_city, next_city) in forbidden_moves:
                    continue
            if len(itinerary) >= 2:
                if itinerary[-2] == itinerary[-1] == next_city:
                    if not (len(itinerary) == 11 and next_city == 'London'):
                        continue
            new_visited = visited | {next_city}
            new_itinerary = itinerary + [next_city]
            res = dfs(new_itinerary, new_visited)
            if res is not None:
                return res
        return None

    start_itinerary = ['London']
    start_visited = {'London'}
    solution = dfs(start_itinerary, start_visited)
    
    if solution is None:
        print("No solution found")
    else:
        segments = []
        start_index = 0
        n = len(solution)
        for i in range(1, n):
            if solution[i] != solution[i-1]:
                segments.append({'place': solution[start_index], 'start': start_index+1, 'end': i})
                start_index = i
        segments.append({'place': solution[start_index], 'start': start_index+1, 'end': n})
        print(segments)

if __name__ == "__main__":
    main()