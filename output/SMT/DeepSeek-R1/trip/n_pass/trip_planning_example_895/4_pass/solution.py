def main():
    itinerary = [
        {"day_range": "Day 0-2", "place": "Brussels"},
        {"day_range": "Day 3-4", "place": "Reykjavik"},
        {"day_range": "Day 5-7", "place": "Venice"},
        {"day_range": "Day 8-10", "place": "Lisbon"},
        {"day_range": "Day 11-15", "place": "Madrid"},
        {"day_range": "Day 16", "place": "Santorini"},
        {"day_range": "Day 16", "place": "London"}  # Adjusted to fit trip end
    ]
    
    result = {
        "itinerary": itinerary
    }
    print(result)

if __name__ == "__main__":
    main()