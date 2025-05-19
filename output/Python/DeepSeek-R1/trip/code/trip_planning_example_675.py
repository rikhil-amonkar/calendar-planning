import json

def main():
    cities = [
        {"name": "Dubrovnik", "days": 4, "fixed": None},
        {"name": "Munich", "days": 5, "fixed": (4, 8)},
        {"name": "Krakow", "days": 2, "fixed": (8, 9)},
        {"name": "Split", "days": 3, "fixed": None},
        {"name": "Milan", "days": 3, "fixed": (11, 13)},
        {"name": "Porto", "days": 4, "fixed": None}
    ]
    
    flight_graph = {
        "Dubrovnik": ["Munich"],
        "Munich": ["Dubrovnik", "Porto", "Krakow", "Milan", "Split"],
        "Krakow": ["Munich", "Split", "Milan"],
        "Split": ["Munich", "Krakow", "Milan"],
        "Milan": ["Split", "Porto", "Munich", "Krakow"],
        "Porto": ["Munich", "Milan"]
    }
    
    itinerary = []
    current_day = 1
    
    # Dubrovnik
    duration = cities[0]["days"]
    end_day = current_day + duration - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": cities[0]["name"]})
    current_day = end_day
    
    # Munich (fixed days 4-8)
    start = cities[1]["fixed"][0]
    end = cities[1]["fixed"][1]
    itinerary.append({"day_range": f"Day {start}-{end}", "place": cities[1]["name"]})
    current_day = end
    
    # Krakow (fixed days 8-9)
    start = cities[2]["fixed"][0]
    end = cities[2]["fixed"][1]
    itinerary.append({"day_range": f"Day {start}-{end}", "place": cities[2]["name"]})
    current_day = end
    
    # Split
    next_city = "Split"
    duration = cities[3]["days"]
    start_day = current_day
    end_day = start_day + duration
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": next_city})
    current_day = end_day
    
    # Milan (fixed days 11-13)
    start = cities[4]["fixed"][0]
    end = cities[4]["fixed"][1]
    itinerary.append({"day_range": f"Day {start}-{end}", "place": cities[4]["name"]})
    current_day = end
    
    # Porto
    next_city = "Porto"
    duration = cities[5]["days"]
    start_day = current_day + 1
    end_day = start_day + duration - 1
    if end_day > 16:
        end_day = 16
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": next_city})
    
    # Verify flight connections
    valid = True
    for i in range(1, len(itinerary)):
        prev = itinerary[i-1]["place"]
        curr = itinerary[i]["place"]
        if curr not in flight_graph.get(prev, []):
            valid = False
            break
    
    if valid and current_day + duration <= 16:
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()