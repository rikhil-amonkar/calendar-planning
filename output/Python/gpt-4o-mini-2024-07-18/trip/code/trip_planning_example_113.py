import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    naples_days = 3
    seville_days = 4
    seville_event_days = 4  # From day 9 to day 12
    milan_days = 7
    
    # Calculate free days
    remaining_days = total_days - (naples_days + seville_days + seville_event_days + milan_days)

    # Days in each city
    naples = {'days': naples_days, 'place': 'Naples'}
    milan = {'days': milan_days, 'place': 'Milan'}
    seville = {'days': seville_days + seville_event_days, 'place': 'Seville'}
    
    # Itinerary plan
    itinerary = []
    
    # Naples: Days 1 to 3
    start_day = 1
    end_day = start_day + naples['days'] - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': naples['place']})

    # Travel from Naples to Milan: Day 4
    start_day += naples['days']
    itinerary.append({'flying': f'Day {start_day}-{start_day}', 'from': naples['place'], 'to': milan['place']})

    # Milan: Days 4 to 10
    end_day = start_day + milan['days'] - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': milan['place']})

    # Travel from Milan to Seville: Day 10
    start_day += milan['days']
    itinerary.append({'flying': f'Day {start_day}-{start_day}', 'from': milan['place'], 'to': seville['place']})

    # Seville: Days 10 to 12 (attending annual show)
    start_day += 1
    end_day = start_day + seville['days'] - 1
    itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': seville['place']})

    return json.dumps(itinerary, indent=4)

# Output the itinerary as JSON
if __name__ == "__main__":
    output = calculate_itinerary()
    print(output)