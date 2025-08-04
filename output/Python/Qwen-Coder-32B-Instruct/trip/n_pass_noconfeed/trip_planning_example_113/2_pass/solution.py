import json

def calculate_itinerary():
    # Input variables
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 7
    seville_show_start_day = 9
    seville_show_end_day = 12

    # Initialize itinerary
    itinerary = []

    # Start in Naples for the first 3 days
    itinerary.append({"day_range": f"Day 1-{naples_days}", "place": "Naples"})

    # Transition to Milan on Day 4 (Day 3 end in Naples, Day 4 start in Milan)
    milan_start_day = naples_days
    milan_end_day = milan_start_day + milan_days - 1

    # Check if Milan can accommodate the required days including overlap with Seville show
    if milan_end_day >= seville_show_start_day:
        # Adjust Milan stay to end just before Seville show starts
        milan_end_day = seville_show_start_day - 1
        milan_days_included = milan_end_day - milan_start_day + 1

        # Add Milan part 1 to itinerary
        itinerary.append({"day_range": f"Day {milan_start_day}-{milan_end_day}", "place": "Milan"})

        # Transition to Seville on Day 8 (Day 7 end in Milan, Day 8 start in Seville)
        seville_start_day = milan_end_day + 1

        # Add Seville show period to itinerary
        itinerary.append({"day_range": f"Day {seville_show_start_day}-{seville_show_end_day}", "place": "Seville"})

        # Calculate remaining days in Seville after the show
        remaining_seville_days = seville_days - (seville_show_end_day - seville_show_start_day + 1)

        # Add remaining Seville days to itinerary if any
        if remaining_seville_days > 0:
            seville_end_day = seville_show_end_day + remaining_seville_days
            itinerary.append({"day_range": f"Day {seville_show_end_day + 1}-{seville_end_day}", "place": "Seville"})
        else:
            seville_end_day = seville_show_end_day

        # Calculate remaining days in Milan after Seville show ends
        remaining_milan_days = milan_days - milan_days_included - remaining_seville_days

        # Add remaining Milan days to itinerary if any
        if remaining_milan_days > 0:
            milan_end_day = seville_end_day + 1
            itinerary.append({"day_range": f"Day {seville_end_day + 1}-{milan_end_day}", "place": "Milan"})
    else:
        # If Milan can accommodate all days without overlapping with Seville show
        itinerary.append({"day_range": f"Day {milan_start_day}-{milan_end_day}", "place": "Milan"})

        # Transition to Seville on Day 8 (Day 7 end in Milan, Day 8 start in Seville)
        seville_start_day = milan_end_day + 1
        seville_end_day = seville_start_day + seville_days - 1

        # Add Seville to itinerary
        itinerary.append({"day_range": f"Day {seville_start_day}-{seville_end_day}", "place": "Seville"})

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Execute the function and print the result
print(calculate_itinerary())