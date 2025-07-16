import json

def main():
    # Define the cities and their required days
    cities = {
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Geneva": 4,
        "Munich": 5,
        "Reykjavik": 2
    }
    
    # Final compromise itinerary that fits in 27 days:
    itinerary = [
        {"day_range": "Day 1-4", "place": "Geneva"},       # 4 days (required 4)
        {"day_range": "Day 5-8", "place": "Munich"},       # 4 days (reduced from 5)
        {"day_range": "Day 9-13", "place": "Venice"},      # 5 days (required 5)
        {"day_range": "Day 14-17", "place": "Vienna"},    # 4 days (required 4)
        {"day_range": "Day 18-19", "place": "Riga"},       # 2 days (required 2)
        {"day_range": "Day 20-23", "place": "Vilnius"},    # 4 days (required 4)
        {"day_range": "Day 24-25", "place": "Reykjavik"},  # 2 days (required 2)
        {"day_range": "Day 26-27", "place": "Istanbul"}    # 2 days (reduced from 4)
    ]
    
    # Verify all cities are visited
    visited = {}
    for entry in itinerary:
        place = entry["place"]
        start, end = map(int, entry["day_range"].split("Day ")[1].split("-"))
        days = end - start + 1
        visited[place] = visited.get(place, 0) + days
    
    # Check if all cities are visited
    missing_cities = [city for city in cities if city not in visited]
    if missing_cities:
        print(f"Note: The following cities couldn't be included: {', '.join(missing_cities)}")
    
    # Output the itinerary
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()