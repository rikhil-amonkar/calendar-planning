import json

def main():
    itinerary = [
        {"day_range": "Day 1-4", "place": "Tallinn"},
        {"day_range": "Day 4-6", "place": "Munich"},
        {"day_range": "Day 6-8", "place": "Manchester"},
        {"day_range": "Day 8-10", "place": "Santorini"},
        {"day_range": "Day 10-13", "place": "Venice"},
        {"day_range": "Day 13-18", "place": "Vienna"},
        {"day_range": "Day 18-20", "place": "Valencia"},
        {"day_range": "Day 20-23", "place": "Porto"},
        {"day_range": "Day 23-24", "place": "Bucharest"},
        {"day_range": "Day 24-24", "place": "Reykjavik"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()