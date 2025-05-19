import json

def calculate_trip_plan(brussels_days, bucharest_days, stuttgart_days, mykonos_days, madrid_days, helsinki_days, split_days, london_days, friend_meeting_window, conference_window):
    total_days = brussels_days + bucharest_days + stuttgart_days + mykonos_days + madrid_days + helsinki_days + split_days + london_days

    # Calculate the number of days for each city, considering the friend meeting window in Stuttgart
    stuttgart_start_day = 1
    stuttgart_end_day = stuttgart_start_day + stuttgart_days - 1
    friend_meeting_day = (friend_meeting_window[0] + friend_meeting_window[1]) // 2

    # Ensure Stuttgart is visited first to meet the friend
    if friend_meeting_day < stuttgart_start_day or friend_meeting_day > stuttgart_end_day:
        raise ValueError("Friend meeting day does not fall within the Stuttgart visit window")

    # Calculate the day ranges for Split
    split_start_day = stuttgart_end_day + 1
    split_end_day = split_start_day + split_days - 1

    # Calculate the day ranges for Mykonos
    mykonos_start_day = split_end_day + 1
    mykonos_end_day = mykonos_start_day + mykonos_days - 1

    # Calculate the day ranges for London
    london_start_day = mykonos_end_day + 1
    london_end_day = london_start_day + london_days - 1

    # Calculate the day ranges for Brussels
    brussels_start_day = london_end_day + 1
    brussels_end_day = brussels_start_day + brussels_days - 1

    # Calculate the day ranges for Bucharest
    bucharest_start_day = brussels_end_day + 1
    bucharest_end_day = bucharest_start_day + bucharest_days - 1

    # Calculate the day ranges for Helsinki
    helsinki_start_day = bucharest_end_day + 1
    helsinki_end_day = helsinki_start_day + helsinki_days - 1

    # Calculate the day ranges for Madrid
    madrid_start_day = helsinki_end_day + 1
    madrid_end_day = madrid_start_day + madrid_days - 1
    conference_day = (conference_window[0] + conference_window[1]) // 2

    # Ensure Madrid is visited last to attend the conference
    if conference_day < madrid_start_day or conference_day > madrid_end_day:
        raise ValueError("Conference day does not fall within the Madrid visit window")

    # Check if the total days add up correctly
    if madrid_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {stuttgart_start_day}-{stuttgart_end_day}', 'place': 'Stuttgart'},
        {'flying': f'Day {stuttgart_end_day}-{stuttgart_end_day}', 'from': 'Stuttgart', 'to': 'Split'},
        {'day_range': f'Day {split_start_day}-{split_end_day}', 'place': 'Split'},
        {'flying': f'Day {split_end_day}-{split_end_day}', 'from': 'Split', 'to': 'Mykonos'},
        {'day_range': f'Day {mykonos_start_day}-{mykonos_end_day}', 'place': 'Mykonos'},
        {'flying': f'Day {mykonos_end_day}-{mykonos_end_day}', 'from': 'Mykonos', 'to': 'London'},
        {'day_range': f'Day {london_start_day}-{london_end_day}', 'place': 'London'},
        {'flying': f'Day {london_end_day}-{london_end_day}', 'from': 'London', 'to': 'Brussels'},
        {'day_range': f'Day {brussels_start_day}-{brussels_end_day}', 'place': 'Brussels'},
        {'flying': f'Day {brussels_end_day}-{brussels_end_day}', 'from': 'Brussels', 'to': 'Bucharest'},
        {'day_range': f'Day {bucharest_start_day}-{bucharest_end_day}', 'place': 'Bucharest'},
        {'flying': f'Day {bucharest_end_day}-{bucharest_end_day}', 'from': 'Bucharest', 'to': 'Helsinki'},
        {'day_range': f'Day {helsinki_start_day}-{helsinki_end_day}', 'place': 'Helsinki'},
        {'flying': f'Day {helsinki_end_day}-{helsinki_end_day}', 'from': 'Helsinki', 'to': 'Madrid'},
        {'day_range': f'Day {madrid_start_day}-{madrid_end_day}', 'place': 'Madrid'}
    ]

    return trip_plan

def main():
    brussels_days = 4
    bucharest_days = 3
    stuttgart_days = 4
    mykonos_days = 2
    madrid_days = 2
    helsinki_days = 5
    split_days = 3
    london_days = 5
    friend_meeting_window = (1, 4)
    conference_window = (20, 21)

    trip_plan = calculate_trip_plan(brussels_days, bucharest_days, stuttgart_days, mykonos_days, madrid_days, helsinki_days, split_days, london_days, friend_meeting_window, conference_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()