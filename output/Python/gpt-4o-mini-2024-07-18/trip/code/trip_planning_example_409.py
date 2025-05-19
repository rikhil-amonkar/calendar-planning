import json

def plan_trip():
    # Define travel constraints and durations
    days = 12
    itinerary = []

    # Defining cities to visit with their respective durations
    stays = {
        'Hamburg': 2,
        'Zurich': 3,  # wedding day between day 1 and day 3
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7   # conferences on day 4 and day 10
    }

    # Initialize current day
    current_day = 1

    # Start with Zurich to accommodate the wedding
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Zurich"] - 1}', 'place': 'Zurich'})
    current_day += stays['Zurich']

    # Transition to Hamburg from Zurich
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Zurich', 'to': 'Hamburg'})
    # Now stay in Hamburg
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Hamburg"] - 1}', 'place': 'Hamburg'})
    current_day += stays['Hamburg']
    
    # Transition to Helsinki from Hamburg
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Hamburg', 'to': 'Helsinki'})
    # Now stay in Helsinki
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Helsinki"] - 1}', 'place': 'Helsinki'})
    current_day += stays['Helsinki']

    # Transition to Bucharest from Helsinki
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Helsinki', 'to': 'Bucharest'})
    # Now stay in Bucharest
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Bucharest"] - 1}', 'place': 'Bucharest'})
    current_day += stays['Bucharest']

    # Transition to Split from Bucharest
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Split'})
    # Now stay in Split, including conference days
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Split"] - 1}', 'place': 'Split'})

    # Return the complete itinerary as a JSON-formatted dictionary
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_itinerary = plan_trip()
    print(trip_itinerary)