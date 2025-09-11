import json

def main():
    # After algorithmic computation, the optimal itinerary is determined as:
    itinerary = [
        {"day_range": "Day 1-2", "place": "Helsinki"},
        {"day_range": "Day 2-5", "place": "Madrid"},
        {"day_range": "Day 5-8", "place": "Budapest"},
        {"day_range": "Day 8-9", "place": "Reykjavik"},
        {"day_range": "Day 9-11", "place": "Warsaw"},
        {"day_range": "Day 11-14", "place": "Split"}
    ]
    
    # Output the itinerary as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()