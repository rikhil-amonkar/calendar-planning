import json

def compute_itinerary():
    # Input parameters
    total_days = 11
    days_in_seville = 6
    days_in_paris = 2
    days_in_krakow = 5
    workshop_days = (1, 5)  # Between Day 1 and Day 5

    # Initialize itinerary and available days
    itinerary = []
    day_counter = 1
    
    # Schedule for Krakow with workshop
    if day_counter < workshop_days[1] + 1:  # Attend workshop in Krakow
        day_range = f"Day {day_counter}-{day_counter + days_in_krakow - 1}"
        itinerary.append({'day_range': day_range, 'place': 'Krakow'})
        day_counter += days_in_krakow

    # Travel from Krakow to Paris
    if day_counter <= total_days:
        itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Krakow', 'to': 'Paris'})
        day_counter += 1

    # Schedule for Paris
    if day_counter < total_days:
        day_range = f"Day {day_counter}-{day_counter + days_in_paris - 1}"
        itinerary.append({'day_range': day_range, 'place': 'Paris'})
        day_counter += days_in_paris

    # Travel from Paris to Seville
    if day_counter <= total_days:
        itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Paris', 'to': 'Seville'})
        day_counter += 1

    # Schedule for Seville
    if day_counter <= total_days:
        day_range = f"Day {day_counter}-{day_counter + days_in_seville - 1}"
        itinerary.append({'day_range': day_range, 'place': 'Seville'})
    
    # Ensure the total days used is 11
    if day_counter <= total_days:
        final_days = total_days - (day_counter - 1)
        if final_days > 0:
            itinerary.append({'day_range': f'Day {day_counter}-{total_days}', 'place': 'Leisure/Explore D1 or D2'})  # Placeholder for end

    return json.dumps(itinerary, indent=4)

# Call the function and print the JSON itinerary
if __name__ == "__main__":
    result = compute_itinerary()
    print(result)