import json

def calculate_trip_plan(bucharest_days, venice_days, prague_days, frankfurt_days, zurich_days, florence_days, tallinn_days, friend_meeting_window, wedding_window, annual_show_window):
    total_days = bucharest_days + venice_days + prague_days + frankfurt_days + zurich_days + florence_days + tallinn_days

    # Calculate the number of days for each city, considering the friend meeting window in Tallinn
    tallinn_start_day = 1
    tallinn_end_day = tallinn_start_day + tallinn_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Tallinn is visited first to meet friends
    if friend_meeting_day < tallinn_start_day or friend_meeting_day > tallinn_end_day:
        raise ValueError("Friend meeting day does not fall within the Tallinn visit window")

    # Calculate the day ranges for Frankfurt
    frankfurt_start_day = tallinn_end_day + 1
    frankfurt_end_day = frankfurt_start_day + frankfurt_days - 1
    annual_show_day = (annual_show_window[0] + annual_show_window[1]) // 2

    # Ensure Frankfurt is visited to attend the annual show
    if annual_show_day < frankfurt_start_day or annual_show_day > frankfurt_end_day:
        raise ValueError("Annual show day does not fall within the Frankfurt visit window")

    # Calculate the day ranges for Prague
    prague_start_day = frankfurt_end_day + 1
    prague_end_day = prague_start_day + prague_days - 1

    # Calculate the day ranges for Bucharest
    bucharest_start_day = prague_end_day + 1
    bucharest_end_day = bucharest_start_day + bucharest_days - 1

    # Calculate the day ranges for Zurich
    zurich_start_day = bucharest_end_day + 1
    zurich_end_day = zurich_start_day + zurich_days - 1

    # Calculate the day ranges for Florence
    florence_start_day = zurich_end_day + 1
    florence_end_day = florence_start_day + florence_days - 1

    # Calculate the day ranges for Venice
    venice_start_day = florence_end_day + 1
    venice_end_day = venice_start_day + venice_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Venice is visited last to attend the wedding
    if wedding_day < venice_start_day or wedding_day > venice_end_day:
        raise ValueError("Wedding day does not fall within the Venice visit window")

    # Check if the total days add up correctly
    if venice_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {tallinn_start_day}-{tallinn_end_day}', 'place': 'Tallinn'},
        {'flying': f'Day {tallinn_end_day}-{tallinn_end_day}', 'from': 'Tallinn', 'to': 'Frankfurt'},
        {'day_range': f'Day {frankfurt_start_day}-{frankfurt_end_day}', 'place': 'Frankfurt'},
        {'flying': f'Day {frankfurt_end_day}-{frankfurt_end_day}', 'from': 'Frankfurt', 'to': 'Prague'},
        {'day_range': f'Day {prague_start_day}-{prague_end_day}', 'place': 'Prague'},
        {'flying': f'Day {prague_end_day}-{prague_end_day}', 'from': 'Prague', 'to': 'Bucharest'},
        {'day_range': f'Day {bucharest_start_day}-{bucharest_end_day}', 'place': 'Bucharest'},
        {'flying': f'Day {bucharest_end_day}-{bucharest_end_day}', 'from': 'Bucharest', 'to': 'Zurich'},
        {'day_range': f'Day {zurich_start_day}-{zurich_end_day}', 'place': 'Zurich'},
        {'flying': f'Day {zurich_end_day}-{zurich_end_day}', 'from': 'Zurich', 'to': 'Florence'},
        {'day_range': f'Day {florence_start_day}-{florence_end_day}', 'place': 'Florence'},
        {'flying': f'Day {florence_end_day}-{florence_end_day}', 'from': 'Florence', 'to': 'Venice'},
        {'day_range': f'Day {venice_start_day}-{venice_end_day}', 'place': 'Venice'}
    ]

    return trip_plan

def main():
    bucharest_days = 3
    venice_days = 5
    prague_days = 4
    frankfurt_days = 5
    zurich_days = 5
    florence_days = 5
    tallinn_days = 5
    friend_meeting_window = (8, 12)
    wedding_window = (22, 26)
    annual_show_window = (12, 16)

    trip_plan = calculate_trip_plan(bucharest_days, venice_days, prague_days, frankfurt_days, zurich_days, florence_days, tallinn_days, friend_meeting_window, wedding_window, annual_show_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()