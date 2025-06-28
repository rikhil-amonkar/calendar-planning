import json

def main():
    itinerary = []
    
    # Fixed part of the itinerary
    itinerary.append({"day_range": "Day 1-3", "place": "London"})
    itinerary.append({"day_range": "Day 3-7", "place": "Milan"})
    itinerary.append({"day_range": "Day 7-9", "place": "Zurich"})
    itinerary.append({"day_range": "Day 9-13", "place": "Reykjavik"})
    
    # Remaining cities with adjusted days
    remaining_cities = [
        {"name": "Stockholm", "days": 1},
        {"name": "Tallinn", "days": 4},
        {"name": "Barcelona", "days": 4},
        {"name": "Stuttgart", "days": 4},
        {"name": "Hamburg", "days": 5},
        {"name": "Bucharest", "days": 2}
    ]
    
    # Start from day 14
    current_day = 14
    for idx, city in enumerate(remaining_cities):
        if idx == 0:
            start_day = current_day
            end_day = current_day + city["days"] - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city["name"]})
            current_day = end_day
        else:
            start_day = current_day
            end_day = current_day + city["days"] - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city["name"]})
            current_day = end_day
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()