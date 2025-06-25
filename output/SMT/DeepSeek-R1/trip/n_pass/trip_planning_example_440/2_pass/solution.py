def main():
    forbidden_moves = {('Paris', 'Rome'), ('Rome', 'Paris'), ('London', 'Berlin'), ('Berlin', 'London')}
    cities = ['London', 'Paris', 'Rome', 'Berlin']
    
    def dfs(d, itinerary, visited):
        if d == 12:
            if itinerary[11] != 'London':
                return None
            if visited == set(cities):
                return itinerary
            else:
                return None
        
        current_city = itinerary[d-1]
        for next_city in cities:
            if next_city != current_city:
                if (current_city, next_city) in forbidden_moves:
                    continue
                    
            if d >= 2:
                if itinerary[d-2] == current_city == next_city:
                    if next_city != 'London':
                        continue
                    else:
                        if visited != set(cities):
                            continue
                        else:
                            sol = itinerary[:]
                            sol.extend(['London'] * (12 - d))
                            return sol
                            
            new_visited = visited | {next_city}
            new_itinerary = itinerary[:]
            new_itinerary.append(next_city)
            
            res = dfs(d+1, new_itinerary, new_visited)
            if res is not None:
                return res
                
        return None
        
    start_itinerary = ['London']
    start_visited = {'London'}
    solution = dfs(1, start_itinerary, start_visited)
    
    if solution is None:
        print("No solution found")
    else:
        print(solution)

if __name__ == "__main__":
    main()