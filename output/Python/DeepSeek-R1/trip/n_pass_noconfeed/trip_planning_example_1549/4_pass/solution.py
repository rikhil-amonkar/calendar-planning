import json

def main():
    city_durations = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    graph = {
        "Prague": ["Riga", "Tallinn", "Warsaw", "Milan", "Stockholm"],
        "Tallinn": ["Riga", "Prague", "Stockholm", "Warsaw"],
        "Warsaw": ["Naples", "Lisbon", "Stockholm", "Riga", "Prague", "Tallinn", "Milan", "Porto"],
        "Porto": ["Lisbon", "Milan", "Warsaw"],
        "Naples": ["Warsaw", "Milan", "Lisbon", "Santorini"],
        "Milan": ["Stockholm", "Riga", "Naples", "Porto", "Prague", "Lisbon", "Warsaw", "Santorini"],
        "Lisbon": ["Stockholm", "Warsaw", "Naples", "Riga", "Porto", "Prague", "Milan"],
        "Santorini": ["Stockholm", "Milan", "Naples"],
        "Riga": ["Prague", "Tallinn", "Warsaw", "Stockholm", "Milan", "Lisbon"],
        "Stockholm": ["Milan", "Lisbon", "Warsaw", "Riga", "Tallinn", "Prague", "Santorini"]
    }
    
    memo = {}
    city_list = list(city_durations.keys())
    
    def dfs(day, visited, last_city):
        if day > 28:
            if "Riga" in visited:
                return []
            else:
                return None
                
        key = (day, frozenset(visited), last_city)
        if key in memo:
            return memo[key]
            
        best_plan = None
        best_length = -1
        
        for city in city_list:
            if city in visited:
                continue
                
            dur = city_durations[city]
            end_day = day + dur - 1
            if end_day > 28:
                continue
                
            if last_city is not None and city not in graph[last_city]:
                continue
                
            if city == "Riga":
                if not (day <= 5 and end_day >= 5):
                    continue
            else:
                if day <= 5 and end_day >= 5:
                    continue
                    
            if city == "Tallinn":
                if not (day <= 20 and end_day >= 18):
                    continue
                    
            if city == "Milan":
                if not (day <= 26 and end_day >= 24):
                    continue
                    
            new_visited = set(visited)
            new_visited.add(city)
            new_visited_frozen = frozenset(new_visited)
            res = dfs(end_day + 1, new_visited_frozen, city)
            
            if res is not None:
                candidate_plan = [{"start": day, "end": end_day, "place": city}] + res
                candidate_length = len(candidate_plan)
                if candidate_length > best_length:
                    best_plan = candidate_plan
                    best_length = candidate_length
                    
        if best_plan is not None:
            memo[key] = best_plan
            return best_plan
            
        if "Riga" in visited:
            memo[key] = []
            return []
        else:
            memo[key] = None
            return None
            
    start_visited = frozenset()
    plan = dfs(1, start_visited, None)
    
    if plan is not None:
        itinerary = []
        for block in plan:
            s = block["start"]
            e = block["end"]
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range_str, "place": block["place"]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()