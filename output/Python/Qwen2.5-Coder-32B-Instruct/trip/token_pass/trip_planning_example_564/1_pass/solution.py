import json

def create_itinerary():
    # Initialize the itinerary list
    itinerary = []
    
    # Define the fixed elements
    istanbul_days = (6, 7)  # Day 6 to Day 7 inclusive
    santorini_days = (13, 16)  # Day 13 to Day 16 inclusive
    
    # Add Istanbul stay
    itinerary.append({"day_range": f"Day {istanbul_days[0]}-{istanbul_days[1]}", "place": "Istanbul"})
    
    # Add Santorini stay
    itinerary.append({"day_range": f"Day {santorini_days[0]}-{santorini_days[1]}", "place": "Santorini"})
    
    # Determine remaining days for other cities
    # Total days: 16
    # Istanbul: 2 days (Day 6-7)
    # Santorini: 4 days (Day 13-16)
    # Remaining days: 16 - 2 - 4 = 10 days
    
    # We need to fit:
    # Rome: 3 days
    # Seville: 4 days
    # Naples: 7 days (but we only have 10 days left, so Naples will partially overlap with other cities)
    
    # Let's place Seville first, since it has a direct connection to Rome
    seville_start_day = 2  # Starting from Day 2
    seville_end_day = seville_start_day + 3  # 4 days in Seville
    itinerary.append({"day_range": f"Day {seville_start_day}-{seville_end_day - 1}", "place": "Seville"})
    
    # Now, let's place Rome, which can be connected to Seville and Naples
    rome_start_day = seville_end_day - 1  # Overlap with Seville on the last day
    rome_end_day = rome_start_day + 4  # 3 days in Rome
    itinerary.append({"day_range": f"Day {rome_start_day}-{rome_end_day - 1}", "place": "Rome"})
    
    # Finally, let's place Naples, which can be connected to Rome and Santorini
    naples_start_day = rome_end_day - 1  # Overlap with Rome on the last day
    naples_end_day = min(naples_start_day + 7, santorini_days[0] - 1)  # 7 days in Naples, but not overlapping with Santorini
    itinerary.append({"day_range": f"Day {naples_start_day}-{naples_end_day}", "place": "Naples"})
    
    # Sort the itinerary by day range start
    itinerary.sort(key=lambda x: int(x['day_range'].split()[1].split('-')[0]))
    
    # Output the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Generate the itinerary
result = create_itinerary()

# Print the result as JSON
print(json.dumps(result, indent=4))