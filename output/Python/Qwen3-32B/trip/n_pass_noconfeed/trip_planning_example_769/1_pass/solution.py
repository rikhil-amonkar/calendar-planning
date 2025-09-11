import json

def main():
    # Define cities and required stays
    cities = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }

    # Define direct flight connections
    flights = {
        "Porto": ["Amsterdam", "Munich"],
        "Amsterdam": ["Porto", "Munich", "Reykjavik", "Santorini", "Prague"],
        "Munich": ["Porto", "Amsterdam", "Reykjavik", "Prague"],
        "Reykjavik": ["Amsterdam", "Munich", "Prague"],
        "Prague": ["Reykjavik", "Amsterdam", "Munich"],
        "Santorini": ["Amsterdam"]
    }

    # Define constraints
    constraints = {
        "Reykjavik_wedding": {"start": 4, "end": 7},
        "Munich_meeting": {"start": 7, "end": 10},
        "Amsterdam_conference": {"start": 14, "end": 15}
    }

    # Initialize itinerary
    itinerary = []
    current_day = 1
    current_city = "Porto"
    remaining_days = cities[current_city]

    # Add Porto
    end_day = current_day + remaining_days - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": current_city})
    current_day = end_day + 1
    remaining_days = 0

    # Next city: Munich (direct flight from Porto)
    current_city = "Munich"
    remaining_days = cities[current_city]
    # Ensure Munich stay overlaps with day 7-10
    start_day = max(current_day, 7 - remaining_days + 1)
    end_day = start_day + remaining_days - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
    current_day = end_day + 1
    remaining_days = 0

    # Next city: Reykjavik (direct flight from Munich)
    current_city = "Reykjavik"
    remaining_days = cities[current_city]
    start_day = current_day
    end_day = start_day + remaining_days - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
    current_day = end_day + 1
    remaining_days = 0

    # Next city: Prague (direct flight from Reykjavik)
    current_city = "Prague"
    remaining_days = cities[current_city]
    start_day = current_day
    end_day = start_day + remaining_days - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
    current_day = end_day + 1
    remaining_days = 0

    # Next city: Amsterdam (direct flight from Prague)
    current_city = "Amsterdam"
    remaining_days = cities[current_city]
    start_day = max(current_day, constraints["Amsterdam_conference"]["start"])
    end_day = start_day + remaining_days - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
    current_day = end_day + 1
    remaining_days = 0

    # Next city: Santorini (direct flight from Amsterdam)
    current_city = "Santorini"
    remaining_days = cities[current_city]
    start_day = current_day
    end_day = start_day + remaining_days - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
    current_day = end_day + 1

    # Output the itinerary
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()