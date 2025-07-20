def main():
    forbidden_moves = {('Paris', 'Rome'), ('Rome', 'Paris'), ('London', 'Berlin'), ('Berlin', 'London')}
    cities = ['Paris', 'Berlin', 'Rome', 'London']
    
    def dfs(itinerary, visited):
        n = len(itinerary)
        if n == 12:
            return itinerary
        
        if n >= 9:
            if n == 9 and set(visited) != set(cities):
                return None
            next_city = 'London'
            current_city = itinerary[-1]
            if next_city != current_city and (current_city, next_city) in forbidden_moves:
                return None
            new_visited = visited | {next_city}
            new_itinerary = itinerary + [next_city]
            return dfs(new_itinerary, new_visited)
            
        else:
            current_city = itinerary[-1]
            for next_city in cities:
                if n == 8 and next_city == 'London':
                    continue
                if next_city != current_city:
                    if (current_city, next_city) in forbidden_moves:
                        continue
                if n >= 2:
                    if itinerary[-2] == itinerary[-1] == next_city:
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
        current_city = solution[0]
        start_day = 1
        for i in range(1, len(solution)):
            if solution[i] != solution[i-1]:
                segments.append({'place': current_city, 'start': start_day, 'end': i})
                current_city = solution[i]
                start_day = i+1
        segments.append({'place': current_city, 'start': start_day, 'end': len(solution)})
        print(segments)

if __name__ == "__main__":
    main()