import json

def main():
    cities = [
        {"name": "London", "days": 4},
        {"name": "Milan", "days": 4},
        {"name": "Zurich", "days": 2},
        {"name": "Reykjavik", "days": 4},
        {"name": "Stockholm", "days": 2},
        {"name": "Tallinn", "days": 2},
        {"name": "Barcelona", "days": 4},
        {"name": "Stuttgart", "days": 2},
        {"name": "Hamburg", "days": 2},
        {"name": "Bucharest", "days": 2}
    ]
    
    itinerary = []
    current_day = 1
    
    for city in cities:
        end_day = current_day + city["days"] - 1
        if current_day == end_day:
            day_range = f"Day {current_day}-{current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city["name"]})
        current_day = end_day + 1
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()