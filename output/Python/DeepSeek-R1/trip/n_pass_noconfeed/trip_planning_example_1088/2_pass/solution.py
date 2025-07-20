import json

def main():
    # Itinerary with adjusted stays
    itinerary = [
        {"day_range": "Day 1-2", "place": "Reykjavik"},
        {"day_range": "Day 3-4", "place": "Stockholm"},
        {"day_range": "Day 5-7", "place": "Split"},      # 3 days
        {"day_range": "Day 8-9", "place": "Geneva"},     # 2 days
        {"day_range": "Day 10-14", "place": "Oslo"},     # 5 days
        {"day_range": "Day 15-18", "place": "Stuttgart"},# 4 days (adjusted)
        {"day_range": "Day 19-21", "place": "Porto"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == '__main__':
    main()