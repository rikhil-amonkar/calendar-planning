import json

def main():
    itinerary = []
    
    # Fixed part with corrected contiguous ranges
    itinerary.append({"day_range": "Day 1-3", "place": "London"})      # 3 days
    itinerary.append({"day_range": "Day 4-7", "place": "Milan"})       # 4 days
    itinerary.append({"day_range": "Day 8-9", "place": "Zurich"})      # 2 days
    itinerary.append({"day_range": "Day 10-13", "place": "Reykjavik"}) # 4 days
    
    # Remaining cities with adjusted days to fit 14 days
    remaining_cities = [
        {"name": "Stockholm", "days": 1},  # Kept as 1 day
        {"name": "Tallinn", "days": 3},    # Reduced from 4 to 3
        {"name": "Barcelona", "days": 3},  # Reduced from 4 to 3
        {"name": "Stuttgart", "days": 3},  # Reduced from 4 to 3
        {"name": "Hamburg", "days": 3},    # Reduced from 5 to 3
        {"name": "Bucharest", "days": 1}   # Reduced from 2 to 1
    ]
    
    # Start from day 15 (14 days: 15-28 inclusive)
    current_day = 15
    for city in remaining_cities:
        end_day = current_day + city["days"] - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}", 
            "place": city["name"]
        })
        current_day = end_day + 1
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()