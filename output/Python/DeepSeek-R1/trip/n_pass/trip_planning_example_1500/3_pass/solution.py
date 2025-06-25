import json

def main():
    cities = [
        {"name": "London", "days": 2},
        {"name": "Milan", "days": 2},
        {"name": "Zurich", "days": 1},
        {"name": "Reykjavik", "days": 2},
        {"name": "Stockholm", "days": 1},
        {"name": "Tallinn", "days": 1},
        {"name": "Barcelona", "days": 2},
        {"name": "Stuttgart", "days": 1},
        {"name": "Hamburg", "days": 1},
        {"name": "Bucharest", "days": 1}
    ]
    
    itinerary = []
    current_day = 1
    
    for city in cities:
        end_day = current_day + city["days"] - 1
        day_range = f"Day {current_day}-{end_day}" if current_day != end_day else f"Day {current_day}-{current_day}"
        itinerary.append({"day_range": day_range, "place": city["name"]})
        current_day = end_day + 1
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()