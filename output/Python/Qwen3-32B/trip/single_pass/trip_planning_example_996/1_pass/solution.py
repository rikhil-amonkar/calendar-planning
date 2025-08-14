import json

def main():
    cities = {
        'Mykonos': 3,
        'Zurich': 5,
        'Prague': 3,
        'Valencia': 5,
        'Bucharest': 5,
        'Riga': 5,
        'Nice': 2
    }

    flights = {
        'Mykonos': ['Nice', 'Zurich'],
        'Zurich': ['Mykonos', 'Nice', 'Riga', 'Bucharest', 'Valencia', 'Prague'],
        'Prague': ['Bucharest', 'Riga', 'Valencia', 'Zurich'],
        'Valencia': ['Bucharest', 'Prague', 'Zurich'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Riga': ['Nice', 'Zurich', 'Bucharest', 'Prague'],
        'Nice': ['Mykonos', 'Riga', 'Zurich']
    }

    def find_valid_path():
        def backtrack(current_path, visited):
            if len(current_path) == 7:
                return current_path.copy()
            current_city = current_path[-1]
            for next_city in flights[current_city]:
                if next_city not in visited:
                    current_path.append(next_city)
                    visited.add(next_city)
                    result = backtrack(current_path, visited)
                    if result is not None:
                        return result
                    current_path.pop()
                    visited.remove(next_city)
            return None

        start_city = 'Mykonos'
        initial_path = [start_city]
        initial_visited = {start_city}
        return backtrack(initial_path, initial_visited)

    def check_prague_constraint(path):
        start_days = []
        end_days = []
        start_day = 1
        end_day = start_day + cities[path[0]] - 1
        start_days.append(start_day)
        end_days.append(end_day)
        
        for i in range(1, len(path)):
            start_day = end_days[i-1]
            duration = cities[path[i]]
            end_day = start_day + duration - 1
            start_days.append(start_day)
            end_days.append(end_day)
        
        prague_index = path.index('Prague') if 'Prague' in path else -1
        if prague_index == -1:
            return False
        
        prague_start = start_days[prague_index]
        prague_end = end_days[prague_index]
        
        return 7 <= prague_start <= 9 and 7 <= prague_end <= 9

    path = find_valid_path()
    if path and check_prague_constraint(path):
        start_days = []
        end_days = []
        start_day = 1
        end_day = start_day + cities[path[0]] - 1
        start_days.append(start_day)
        end_days.append(end_day)
        
        for i in range(1, len(path)):
            start_day = end_days[i-1]
            duration = cities[path[i]]
            end_day = start_day + duration - 1
            start_days.append(start_day)
            end_days.append(end_day)
        
        itinerary = []
        for i in range(len(path)):
            start = start_days[i]
            end = end_days[i]
            city = path[i]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()