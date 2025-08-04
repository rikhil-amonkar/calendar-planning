import json

def calculate_itinerary():
    # Input variables
    total_days = 16
    london_stay = 7
    split_stay = 5
    oslo_stay = 2
    porto_stay = 2

    # Initialize itinerary
    itinerary = []

    # Start in London for the first part of the trip
    itinerary.append({"day_range": f"Day 1-{london_stay}", "place": "London"})

    # Move to Split after London
    itinerary.append({"day_range": f"Day {london_stay + 1}-{london_stay + split_stay}", "place": "Split"})

    # Move to Oslo after Split
    start_oslo_day = london_stay + split_stay + 1
    itinerary.append({"day_range": f"Day {start_oslo_day}-{start_oslo_day + oslo_stay - 1}", "place": "Oslo"})

    # Move to Porto after Oslo
    start_porto_day = start_oslo_day + oslo_stay
    itinerary.append({"day_range": f"Day {start_porto_day}-{start_porto_day + porto_stay - 1}", "place": "Porto"})

    # Remaining days in Porto
    remaining_days_in_porto = total_days - (start_porto_day + porto_stay - 1)
    if remaining_days_in_porto > 0:
        end_porto_day = total_days
        itinerary.append({"day_range": f"Day {start_porto_day + porto_stay}-{end_porto_day}", "place": "Porto"})

    return itinerary

# Calculate and print the itinerary in JSON format
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))