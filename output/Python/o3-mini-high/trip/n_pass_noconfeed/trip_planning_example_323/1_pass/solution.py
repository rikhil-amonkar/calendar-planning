#!/usr/bin/env python3
import json

def main():
    # Trip constraints and input variables
    total_trip_days = 16
    
    # Required number of days to spend (including flight overlap days)
    required_days = {
        "London": 7,
        "Split": 5,
        "Oslo": 2,
        "Porto": 5
    }
    
    # Special event constraints
    # In Split, an annual show runs from Day 7 to Day 11 (Split stay must cover days 7-11)
    split_show_start = 7
    split_show_end = 11
    
    # Visit relatives in London between Day 1 and Day 7 implies presence in London until at least Day 7.
    
    # Direct flight connections (bidirectional)
    direct_flights = {
        ("London", "Oslo"),
        ("Oslo", "London"),
        ("Split", "Oslo"),
        ("Oslo", "Split"),
        ("Oslo", "Porto"),
        ("Porto", "Oslo"),
        ("London", "Split"),
        ("Split", "London")
    }
    
    def flight_available(origin, destination):
        return (origin, destination) in direct_flights
    
    # We decide on an itinerary order based on the constraints and available flights:
    # Start in London, then fly from London to Split, then Split to Oslo, and finally Oslo to Porto.
    # Check that each flight exists:
    route = [
        ("London", "Split"),
        ("Split", "Oslo"),
        ("Oslo", "Porto")
    ]
    for origin, dest in route:
        if not flight_available(origin, dest):
            raise ValueError(f"No direct flight available from {origin} to {dest}.")

    # Calculate itinerary segments.
    # Rule: if we fly from city A to city B on day X, then day X counts for both cities.
    itinerary = []
    current_day = 1

    # London segment: must cover Day 1 up to Day 7.
    london_start = current_day
    # For a required 7 days, if we depart on day 7, then London counts days 1-7.
    london_end = london_start + required_days["London"] - 1  # Day 1 to Day 7
    itinerary.append({
        "day_range": f"Day {london_start}-{london_end}",
        "place": "London"
    })
    
    # Flight from London to Split takes off on Day 7; thus, Split starts on Day 7.
    split_start = london_end  # Day 7 (overlap with London)
    split_end = split_start + required_days["Split"] - 1  # Day 7 to Day 11
    # Ensuring that the Split show constraint is met
    if split_start > split_show_start or split_end < split_show_end:
        raise ValueError("The Split itinerary does not cover the annual show dates.")
    itinerary.append({
        "day_range": f"Day {split_start}-{split_end}",
        "place": "Split"
    })

    # Flight from Split to Oslo on Day 11; Oslo gets Day 11 as well.
    oslo_start = split_end  # Day 11 (overlap with Split)
    oslo_end = oslo_start + required_days["Oslo"] - 1  # Day 11 to Day 12
    itinerary.append({
        "day_range": f"Day {oslo_start}-{oslo_end}",
        "place": "Oslo"
    })

    # Flight from Oslo to Porto on Day 12; Porto gets Day 12 as well.
    porto_start = oslo_end  # Day 12 (overlap with Oslo)
    porto_end = porto_start + required_days["Porto"] - 1  # Day 12 to Day 16
    itinerary.append({
        "day_range": f"Day {porto_start}-{porto_end}",
        "place": "Porto"
    })
    
    # Final check to ensure we exactly cover the total trip days.
    if porto_end != total_trip_days:
        raise ValueError("The computed itinerary does not match the total trip days constraint.")
    
    # Output the itinerary as a JSON-formatted dictionary
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()