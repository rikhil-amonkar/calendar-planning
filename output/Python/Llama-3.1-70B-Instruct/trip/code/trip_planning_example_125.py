import json

def calculate_trip_plan(stuttgart_days, seville_days, manchester_days, friend_meeting_window):
    total_days = stuttgart_days + seville_days + manchester_days

    # Calculate the number of days for each city, considering the friend meeting window in Stuttgart
    stuttgart_start_day = 1
    stuttgart_end_day = stuttgart_start_day + stuttgart_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Stuttgart is visited first to meet the friend
    if friend_meeting_day < stuttgart_start_day or friend_meeting_day > stuttgart_end_day:
        raise ValueError("Friend meeting day does not fall within the Stuttgart visit window")

    # Calculate the day ranges for Seville and Manchester
    seville_start_day = stuttgart_end_day + 1
    seville_end_day = seville_start_day + seville_days - 1
    manchester_start_day = seville_end_day + 1
    manchester_end_day = manchester_start_day + manchester_days - 1

    # Check if the total days add up correctly
    if manchester_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {stuttgart_start_day}-{stuttgart_end_day}', 'place': 'Stuttgart'},
        {'flying': f'Day {stuttgart_end_day}-{stuttgart_end_day}', 'from': 'Stuttgart', 'to': 'Manchester'},
        {'day_range': f'Day {manchester_start_day}-{manchester_end_day}', 'place': 'Manchester'},
        {'flying': f'Day {manchester_end_day}-{manchester_end_day}', 'from': 'Manchester', 'to': 'Seville'},
        {'day_range': f'Day {seville_start_day}-{seville_end_day}', 'place': 'Seville'}
    ]

    # Since Manchester and Seville have direct flights, swap Manchester and Seville
    trip_plan = [
        {'day_range': f'Day {stuttgart_start_day}-{stuttgart_end_day}', 'place': 'Stuttgart'},
        {'flying': f'Day {stuttgart_end_day}-{stuttgart_end_day}', 'from': 'Stuttgart', 'to': 'Manchester'},
        {'day_range': f'Day {stuttgart_end_day+1}-{stuttgart_end_day+manchester_days}', 'place': 'Manchester'},
        {'flying': f'Day {stuttgart_end_day+manchester_days}-{stuttgart_end_day+manchester_days}', 'from': 'Manchester', 'to': 'Seville'},
        {'day_range': f'Day {stuttgart_end_day+manchester_days+1}-{total_days}', 'place': 'Seville'}
    ]

    return trip_plan

def main():
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    friend_meeting_window = (1, 6)

    trip_plan = calculate_trip_plan(stuttgart_days, seville_days, manchester_days, friend_meeting_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()