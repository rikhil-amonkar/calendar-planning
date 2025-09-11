import json

def main():
    # Fixed events
    itinerary = [
        {"day_range": "Day 1-3", "place": "London"},
        {"day_range": "Day 3-7", "place": "Milan"},
        {"day_range": "Day 7-8", "place": "Zurich"},
        {"day_range": "Day 9-13", "place": "Reykjavik"}
    ]
    
    # Remaining cities and their required days
    remaining_cities = [
        {"name": "Stuttgart", "days": 5},
        {"name": "Hamburg", "days": 5},
        {"name": "Stockholm", "days": 2},
        {"name": "Tallinn", "days": 4}
    ]
    
    # Start day for the remaining cities
    current_day = 14
    for city in remaining_cities:
        end_day = current_day + city["days"] - 1
        if end_day > 28:
            end_day = 28
            # Adjust if exceeds total days
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city["name"]
        })
        current_day = end_day + 1
        if current_day > 28:
            break
            
    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()