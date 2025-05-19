import json

def compute_itinerary():
    # Input constraints
    days_total = 28
    cities_constraints = {
        'Copenhagen': {'duration': 5, 'friends_meeting': (11, 15)},
        'Geneva': {'duration': 3},
        'Mykonos': {'duration': 2, 'conference_days': (27, 28)},
        'Naples': {'duration': 4, 'relatives_visit': (5, 8)},
        'Prague': {'duration': 2},
        'Dubrovnik': {'duration': 3},
        'Athens': {'duration': 4, 'workshop_days': (8, 11)},
        'Santorini': {'duration': 5},
        'Brussels': {'duration': 4},
        'Munich': {'duration': 5},
    }
    
    # States of the trip
    itinerary = []
    current_day = 1

    # Helper function to add a portion to the itinerary
    def add_to_itinerary(days, city):
        nonlocal current_day
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days - 1}', 'place': city})
        current_day += days

    # Itinerary computation based on constraints
    # Starting from Copenhagen, since it's the first defined city in constraints
    add_to_itinerary(cities_constraints['Copenhagen']['duration'], 'Copenhagen')
    
    # Visit Naples between days 5-8 for relatives
    add_to_itinerary(cities_constraints['Naples']['duration'], 'Naples')

    # After Naples, attend a workshop in Athens from days 8-11
    add_to_itinerary(cities_constraints['Athens']['duration'], 'Athens')
    
    # Then head to Dubrovnik for 3 days
    add_to_itinerary(cities_constraints['Dubrovnik']['duration'], 'Dubrovnik')
    
    # After Dubrovnik, we can visit Prague for 2 days
    add_to_itinerary(cities_constraints['Prague']['duration'], 'Prague')
    
    # Now go to Geneva for 3 days
    add_to_itinerary(cities_constraints['Geneva']['duration'], 'Geneva')

    # Meet the friend in Copenhagen
    add_to_itinerary(5, 'Copenhagen')  # 5 days, to accommodate friend visit
    
    # After Copenhagen, go to Mykonos. This is before the conference.
    add_to_itinerary(cities_constraints['Mykonos']['duration'], 'Mykonos')
    
    # Now, go to Santorini for 5 days
    add_to_itinerary(cities_constraints['Santorini']['duration'], 'Santorini')
    
    # Finally, go back to Munich for 5 days
    add_to_itinerary(cities_constraints['Munich']['duration'], 'Munich')
    
    # Visit Brussels for the last 4 days
    add_to_itinerary(cities_constraints['Brussels']['duration'], 'Brussels')

    # Add the mandatory conference days
    add_to_itinerary(2, 'Mykonos')  # Days 27-28 in Mykonos for conference

    return itinerary

# Get the computed itinerary
itinerary = compute_itinerary()

# Output itinerary as a JSON-formatted dictionary
print(json.dumps(itinerary, indent=4))