import json

def main():
    cities = {
        "Geneva": 4,
        "Munich": 7,
        "Bucharest": 2,
        "Valencia": 6,
        "Stuttgart": 2
    }
    
    flights = {
        "Geneva": ["Munich", "Valencia"],
        "Munich": ["Geneva", "Valencia", "Bucharest"],
        "Bucharest": ["Munich", "Valencia"],
        "Valencia": ["Geneva", "Munich", "Bucharest", "Stuttgart"],
        "Stuttgart": ["Valencia"]
    }
    
    itinerary_order = ["Geneva", "Munich", "Bucharest", "Valencia", "Stuttgart"]
    
    for i in range(len(itinerary_order)-1):
        if itinerary_order[i+1] not in flights[itinerary_order[i]]:
            raise ValueError("Invalid flight connection")
    
    current_day = 1
    itinerary = []
    for city in itinerary_order:
        days = cities[city]
        end_day = current_day + days - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    
    if itinerary[0]["day_range"] != "Day 1-4":
        raise ValueError("Geneva constraint violated")
    if itinerary[1]["day_range"] != "Day 4-10":
        raise ValueError("Munich constraint violated")
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()