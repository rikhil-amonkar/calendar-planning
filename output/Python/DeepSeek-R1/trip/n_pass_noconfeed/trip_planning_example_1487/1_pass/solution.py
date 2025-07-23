import json

def main():
    required_days = {
        "Copenhagen": 5,
        "Geneva": 3,
        "Mykonos": 2,
        "Naples": 4,
        "Prague": 2,
        "Dubrovnik": 3,
        "Athens": 4,
        "Santorini": 5,
        "Brussels": 4,
        "Munich": 5
    }
    
    direct_flights = [
        "Copenhagen and Dubrovnik",
        "Brussels and Copenhagen",
        "Prague and Geneva",
        "Athens and Geneva",
        "Naples and Dubrovnik",
        "Athens and Dubrovnik",
        "Geneva and Mykonos",
        "Naples and Mykonos",
        "Naples and Copenhagen",
        "Munich and Mykonos",
        "Naples and Athens",
        "Prague and Athens",
        "Santorini and Geneva",
        "Athens and Santorini",
        "Naples and Santorini",
        "Dubrovnik and Munich",
        "Brussels and Munich",
        "Prague and Brussels",
        "Brussels and Athens",
        "Athens and Munich",
        "Geneva and Munich",
        "Copenhagen and Munich",
        "Brussels and Geneva",
        "Copenhagen and Geneva",
        "Prague and Munich",
        "Copenhagen and Santorini",
        "Naples and Santorini",
        "Geneva and Dubrovnik"
    ]
    
    graph = {city: set() for city in required_days}
    for flight in direct_flights:
        city1, city2 = flight.split(" and ")
        graph[city1].add(city2)
        graph[city2].add(city1)
    
    cities = list(required_days.keys())
    n = 10
    order = [None] * n
    order[9] = "Mykonos"
    used = set(["Mykonos"])
    
    def backtrack(index, cumulative, used, order):
        if index == 9:
            if order[8] in graph["Mykonos"]:
                return order[:]
            else:
                return None
                
        for city in cities:
            if city in used:
                continue
            L = required_days[city]
            start_day = 1 + cumulative
            end_day = start_day + L - 1
            
            if city == "Copenhagen":
                if not (start_day <= 15 and end_day >= 11):
                    continue
            elif city == "Naples":
                if not (start_day <= 8 and end_day >= 5):
                    continue
            elif city == "Athens":
                if not (start_day <= 11 and end_day >= 8):
                    continue
            
            if index >= 1:
                prev_city = order[index-1]
                if city not in graph[prev_city]:
                    continue
            
            order[index] = city
            used.add(city)
            new_cumulative = cumulative + (L - 1)
            res_order = backtrack(index+1, new_cumulative, used, order)
            if res_order is not None:
                return res_order
            order[index] = None
            used.remove(city)
            
        return None
        
    solution_order = backtrack(0, 0, used, order)
    if solution_order is None:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary_list = []
    cumulative_days = 0
    for i in range(n):
        city = solution_order[i]
        L = required_days[city]
        start = 1 + cumulative_days
        end = start + L - 1
        cumulative_days += (L - 1)
        day_range_str = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
        
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()