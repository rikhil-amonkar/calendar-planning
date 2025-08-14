import json

def main():
    cities = {
        "Bucharest": {"duration": 4, "start": 1, "end": 4},
        "Munich": {"duration": 5, "start": 4, "end": 8},
        "Seville": {"duration": 5, "start": 8, "end": 12},
        "Milan": {"duration": 2},
        "Stockholm": {"duration": 5},
        "Tallinn": {"duration": 2},
    }
    
    flight_connections = {
        "Bucharest": ["Munich"],
        "Munich": ["Bucharest", "Seville", "Milan", "Stockholm", "Tallinn"],
        "Seville": ["Munich", "Milan"],
        "Milan": ["Seville", "Munich", "Stockholm"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Tallinn": ["Stockholm"],
    }
    
    itinerary = []
    visited = set()
    current_city = "Bucharest"
    current_end_day = cities[current_city]["end"]
    itinerary.append({"city": current_city, "start": cities[current_city]["start"], "end": current_end_day})
    visited.add(current_city)
    
    remaining_cities = [city for city in cities if city != current_city]
    
    while remaining_cities:
        last_city = itinerary[-1]["city"]
        possible_next_cities = [city for city in flight_connections[last_city] if city not in visited]
        
        next_city = None
        for candidate in possible_next_cities:
            if "start" in cities[candidate]:
                required_start = cities[candidate]["start"]
                if current_end_day == required_start:
                    next_city = candidate
                    break
            else:
                next_city = candidate
                break
        
        if next_city is None:
            raise ValueError("No valid next city found")
        
        duration = cities[next_city]["duration"]
        start_day = current_end_day
        end_day = start_day + duration - 1
        itinerary.append({"city": next_city, "start": start_day, "end": end_day})
        visited.add(next_city)
        current_end_day = end_day
        remaining_cities.remove(next_city)
    
    # Convert to the required JSON format
    json_itinerary = []
    for entry in itinerary:
        day_range = f"Day {entry['start']}-{entry['end']}"
        place = entry['city']
        json_itinerary.append({"day_range": day_range, "place": place})
    
    print(json.dumps({"itinerary": json_itinerary}, indent=2))

if __name__ == "__main__":
    main()