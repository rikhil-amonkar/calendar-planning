import json

def compute_itinerary():
    itinerary = []
    day_counter = 1

    # 1. Spend 5 days in Seville
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 4}', 'place': 'Seville'})
    day_counter += 5

    # 2. Visit Vilnius for 3 days
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Seville', 'to': 'Vilnius'})
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Vilnius'})
    day_counter += 3

    # 3. Fly to Frankfurt for 5 days
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Vilnius', 'to': 'Frankfurt'})
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 4}', 'place': 'Frankfurt'})
    day_counter += 5

    # 4. Move to Stuttgart between day 7-9
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Frankfurt', 'to': 'Stuttgart'})
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Stuttgart'})
    day_counter += 3

    # 5. Fly to London (must meet friends between day 9-10)
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Stuttgart', 'to': 'London'})
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 1}', 'place': 'London'})
    day_counter += 2

    # 6. London to Santorini for 2 days
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'London', 'to': 'Santorini'})
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 1}', 'place': 'Santorini'})
    day_counter += 2

    # 7. Back to Dublin for 3 days
    itinerary.append({'flying': f'Day {day_counter}-{day_counter}', 'from': 'Santorini', 'to': 'Dublin'})
    itinerary.append({'day_range': f'Day {day_counter}-{day_counter + 2}', 'place': 'Dublin'})
    day_counter += 3

    # Total days should be 17
    total_days = day_counter - 1
    assert total_days == 17, f'Total days should equal 17, but got {total_days}.'

    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = compute_itinerary()
    print(trip_plan)