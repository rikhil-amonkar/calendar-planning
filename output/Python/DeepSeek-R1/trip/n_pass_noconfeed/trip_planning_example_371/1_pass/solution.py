import json

def main():
    stays = {
        'Vienna': 2,
        'Stockholm': 5,
        'Nice': 2,
        'Split': 3
    }
    
    fixed_events = {
        1: 'Vienna',
        2: 'Vienna',
        7: 'Split',
        9: 'Split'
    }
    
    direct_flights = {
        'Vienna': ['Stockholm', 'Nice', 'Split'],
        'Stockholm': ['Vienna', 'Nice', 'Split'],
        'Nice': ['Vienna', 'Stockholm'],
        'Split': ['Vienna', 'Stockholm']
    }
    
    cities = ['Vienna', 'Stockholm', 'Nice', 'Split']
    
    def dfs(day, current_city, counts, moves):
        if day > 9:
            if all(counts[city] == stays[city] for city in cities):
                return moves
            else:
                return None
                
        options = []
        if day in fixed_events:
            req_city = fixed_events[day]
            if current_city == req_city:
                options.append((current_city, current_city))
        else:
            options.append((current_city, current_city))
            
        for next_city in direct_flights[current_city]:
            if day in fixed_events:
                req_city = fixed_events[day]
                if current_city == req_city or next_city == req_city:
                    options.append((current_city, next_city))
            else:
                options.append((current_city, next_city))
                
        for opt in options:
            new_counts = counts.copy()
            start, end = opt
            new_counts[start] += 1
            if start != end:
                new_counts[end] += 1
                
            if any(new_counts[city] > stays[city] for city in cities):
                continue
                
            new_moves = moves + [opt]
            res = dfs(day+1, end, new_counts, new_moves)
            if res is not None:
                return res
                
        return None
        
    initial_counts = {city: 0 for city in cities}
    moves_result = dfs(1, 'Vienna', initial_counts, [])
    
    if moves_result is None:
        itinerary = []
    else:
        city_days = {city: set() for city in cities}
        for day_index in range(9):
            day_num = day_index + 1
            s, e = moves_result[day_index]
            city_days[s].add(day_num)
            city_days[e].add(day_num)
            
        blocks = []
        for city in cities:
            days_set = city_days[city]
            if days_set:
                min_day = min(days_set)
                max_day = max(days_set)
                blocks.append((min_day, max_day, city))
                
        blocks.sort(key=lambda x: x[0])
        itinerary = []
        for min_day, max_day, city in blocks:
            if min_day == max_day:
                day_range_str = f"Day {min_day}"
            else:
                day_range_str = f"Day {min_day}-{max_day}"
            itinerary.append({"day_range": day_range_str, "place": city})
            
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()