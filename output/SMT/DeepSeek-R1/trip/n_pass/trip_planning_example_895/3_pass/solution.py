def main():
    itinerary = [
        {"day_range": "Day 0", "place": "Brussels"},
        {"day_range": "Day 2", "place": "Reykjavik"},
        {"day_range": "Day 4", "place": "Lisbon"},
        {"day_range": "Day 6", "place": "Venice"},
        {"day_range": "Day 8-11", "place": "Madrid"},
        {"day_range": "Day 13", "place": "Santorini"},
        {"day_range": "Day 15-16", "place": "London"}
    ]
    
    result = {
        "itinerary": itinerary
    }
    print(result)

if __name__ == "__main__":
    main()