import json

def plan_trip():
    # Defining the duration in days for each city
    city_durations = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }

    # Total days for the trip
    total_days = 12
    itinerary = []
    day_counter = 1

    # Split: Days 1-2
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_durations["Split"] - 1}', 'place': 'Split'})
    day_counter += city_durations["Split"]

    # Helsinki: Days 3-4
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_durations["Helsinki"] - 1}', 'place': 'Helsinki'})
    day_counter += city_durations["Helsinki"]

    # Vilnius: Days 5-7
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_durations["Vilnius"] - 1}', 'place': 'Vilnius'})
    day_counter += city_durations["Vilnius"]

    # Reykjavik: Days 8-10
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + city_durations["Reykjavik"] - 1}', 'place': 'Reykjavik'})
    day_counter += city_durations["Reykjavik"]

    # Wedding Days in Reykjavik: Days 10-12
    # This will overlap with the last days in Reykjavik already planned
    
    # Geneva: Adjusting it to fit into the last available days
    # Since the wedding is in Reykjavik on last 2 days, Geneva has to fit within Days 5 to 9
    # Moving Geneva at Day 5 to Day 10 (total 6 days)
    # So it goes back to Day 1-5 as a fit
    itinerary.insert(1, {'day_range': f'Day {day_counter}-{day_counter + city_durations["Geneva"] - 1}', 'place': 'Geneva'})
    day_counter += city_durations["Geneva"]

    # Adding flying details:
    flying_details = [
        {'flying': f'Day 1', 'from': 'Departure', 'to': 'Split'},
        {'flying': f'Day 3', 'from': 'Split', 'to': 'Helsinki'},
        {'flying': f'Day 5', 'from': 'Helsinki', 'to': 'Vilnius'},
        {'flying': f'Day 8', 'from': 'Vilnius', 'to': 'Reykjavik'},
        {'flying': f'Day 10', 'from': 'Reykjavik', 'to': 'Geneva'}, # leaving Geneva after wedding
    ]

    # Combine itinerary with flying details
    full_itinerary = []
    for item in itinerary:
        full_itinerary.append(item)
        if item['place'] == 'Split':
            full_itinerary.extend(flying_details[0:1])
        elif item['place'] == 'Helsinki':
            full_itinerary.extend(flying_details[1:2])
        elif item['place'] == 'Vilnius':
            full_itinerary.extend(flying_details[2:3])
        elif item['place'] == 'Reykjavik':
            full_itinerary.extend(flying_details[3:4])
        elif item['place'] == 'Geneva':
            full_itinerary.extend(flying_details[4:5])
    
    return json.dumps(full_itinerary)

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)