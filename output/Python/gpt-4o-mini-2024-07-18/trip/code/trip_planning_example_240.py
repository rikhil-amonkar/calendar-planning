import json

def plan_trip():
    # Define trip parameters
    total_days = 12
    itinerary = []

    # Days allocated for each city
    prague_days = 2
    berlin_days = 3
    conference_days = [6, 8]  # Conference on day 6 and 8
    tallinn_days = 5
    stockholm_days = 5

    # Define the schedule
    # Starting in Prague
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Prague'})

    # Travel to Berlin for 3 days
    itinerary.append({'flying': 'Day 2-2', 'from': 'Prague', 'to': 'Berlin'})
    itinerary.append({'day_range': 'Day 2-5', 'place': 'Berlin'})

    # Add conference days in Berlin
    # Conference on Day 6 and Day 8, need to return after tallinn
    # Travel to Tallinn after Berlin
    itinerary.append({'flying': 'Day 5-5', 'from': 'Berlin', 'to': 'Tallinn'})
    itinerary.append({'day_range': 'Day 5-10', 'place': 'Tallinn'})

    # Visiting relatives in Tallinn from Day 8 to Day 12
    # So we can allocate the last 5 days in Tallinn

    # Travel to Stockholm after Tallinn
    itinerary.append({'flying': 'Day 10-10', 'from': 'Tallinn', 'to': 'Stockholm'})
    itinerary.append({'day_range': 'Day 10-12', 'place': 'Stockholm'})

    # Consolidate into a 12 day plan
    # The final itinerary looks like:
    final_itinerary = []
    day_count = 0
    for entry in itinerary:
        if 'day_range' in entry:
            days = entry['day_range'].split('-')
            start_day = int(days[0].split(' ')[1])
            end_day = int(days[1])
            day_count += (end_day - start_day + 1)
            final_itinerary.append(entry)
        elif 'flying' in entry:
            final_itinerary.append(entry)

    # Check for total days
    assert day_count == total_days, "Total days should sum up to 12"

    # Output the result as JSON
    return json.dumps(final_itinerary, indent=4)

# Running the trip planner and printing the JSON output
if __name__ == "__main__":
    print(plan_trip())