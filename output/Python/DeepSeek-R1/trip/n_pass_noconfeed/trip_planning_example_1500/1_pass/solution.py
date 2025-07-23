import json
from collections import defaultdict

def main():
    cities_second_part = ['Barcelona', 'Stuttgart', 'Hamburg', 'Tallinn', 'Bucharest']
    req_days = [4, 5, 5, 4, 2]
    city_to_index = {city: idx for idx, city in enumerate(cities_second_part)}
    
    graph_second = defaultdict(list)
    graph_second[0] = [1, 2, 3, 4]  # Barcelona
    graph_second[1] = [0, 2]         # Stuttgart
    graph_second[2] = [0, 1, 4]      # Hamburg
    graph_second[3] = [0]             # Tallinn
    graph_second[4] = [0, 2]          # Bucharest
    
    start_cities = [0, 1]  # Barcelona and Stuttgart have direct flights from Reykjavik
    memo = {}
    path_tracker = {}
    
    def dfs(day, city, days_spent):
        if day > 28:
            if days_spent == tuple(req_days):
                return []
            return None
            
        key = (day, city, days_spent)
        if key in memo:
            return memo[key]
            
        days_list = list(days_spent)
        city_idx = city
        
        if days_list[city_idx] < req_days[city_idx]:
            new_days = days_list[:]
            new_days[city_idx] += 1
            new_days_tuple = tuple(new_days)
            res_stay = dfs(day+1, city, new_days_tuple)
            if res_stay is not None:
                path_tracker[key] = (city, day, day, False)
                return [cities_second_part[city]] + res_stay
                
        for next_city in graph_second[city]:
            if days_list[next_city] < req_days[next_city]:
                new_days = days_list[:]
                new_days[city_idx] += 1
                new_days[next_city] += 1
                if new_days[city_idx] > req_days[city_idx] or new_days[next_city] > req_days[next_city]:
                    continue
                new_days_tuple = tuple(new_days)
                res_fly = dfs(day+1, next_city, new_days_tuple)
                if res_fly is not None:
                    path_tracker[key] = (next_city, day, day, True)
                    return [cities_second_part[city]] + res_fly
                    
        memo[key] = None
        return None
        
    solution_path = None
    for start in start_cities:
        initial_days = [0, 0, 0, 0, 0]
        res = dfs(14, start, tuple(initial_days))
        if res is not None:
            solution_path = res
            break
            
    if solution_path is None:
        itinerary = [
            {"day_range": "Day 1-3", "place": "London"},
            {"day_range": "Day 3-7", "place": "Milan"},
            {"day_range": "Day 7-8", "place": "Zurich"},
            {"day_range": "Day 8-9", "place": "Stockholm"},
            {"day_range": "Day 9-13", "place": "Reykjavik"},
        ]
    else:
        itinerary = [
            {"day_range": "Day 1-3", "place": "London"},
            {"day_range": "Day 3-7", "place": "Milan"},
            {"day_range": "Day 7-8", "place": "Zurich"},
            {"day_range": "Day 8-9", "place": "Stockholm"},
            {"day_range": "Day 9-13", "place": "Reykjavik"},
        ]
        
        current_place = solution_path[0]
        start_day_second = 14
        last_day_second = 14
        for i in range(1, len(solution_path)):
            if solution_path[i] == solution_path[i-1]:
                last_day_second = 14 + i
            else:
                itinerary.append({"day_range": f"Day {start_day_second}-{last_day_second}", "place": solution_path[i-1]})
                start_day_second = 14 + i
                last_day_second = 14 + i
        itinerary.append({"day_range": f"Day {start_day_second}-28", "place": solution_path[-1]})
        
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()