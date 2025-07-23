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
        if len(visited) == len(city_list):
            if day == 29:
                return []
            else:
                return None
                
        key = (day, frozenset(visited), last_city)
        if key in memo:
            return memo[key]
            
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
                if not (day <= 5 and end_day >= 8):
                    continue
                if day != 5:
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
            res = dfs(end_day, frozenset(new_visited), city)
            if res is not None:
                block = {"start": day, "end": end_day, "place": city}
                memo[key] = [block] + res
                return [block] + res
                
        memo[key] = None
        return None
        
    all_cities_set = frozenset(city_list)
    for city in city_list:
        dur = city_durations[city]
        if dur < 5 and city != "Riga":
            res = dfs(1, frozenset([city]), city)
            if res is not None:
                itinerary = []
                for block in res:
                    s = block["start"]
                    e = block["end"]
                    if s == e:
                        day_range_str = f"Day {s}"
                    else:
                        day_range_str = f"Day {s}-{e}"
                    itinerary.append({"day_range": day_range_str, "place": block["place"]})
                print(json.dumps({"itinerary": itinerary}))
                return
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()