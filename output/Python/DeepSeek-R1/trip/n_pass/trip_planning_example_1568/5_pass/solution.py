import json

def main():
    cities = [
        "Vienna",
        "Prague",
        "Split",
        "Amsterdam",
        "Brussels",
        "Riga",
        "Stockholm",
        "Istanbul"
    ]
    stay_days = [2, 2, 2, 2, 2, 1, 1, 1]
    
    itinerary = []
    current_day = 1
    for i in range(len(cities)):
        days = stay_days[i]
        end_day = current_day + days - 1
        day_range = f"Day {current_day}-{end_day}" if days > 1 else f"Day {current_day}"
        itinerary.append({"day_range": day_range, "place": cities[i]})
        
        if i < len(cities) - 1:
            current_day = end_day + 2
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()