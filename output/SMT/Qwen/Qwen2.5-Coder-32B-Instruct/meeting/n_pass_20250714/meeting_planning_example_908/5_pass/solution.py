from datetime import datetime, timedelta

# Define the schedule manually
schedule = [
    ("Mark", datetime(2023, 10, 1, 9, 15), datetime(2023, 10, 1, 9, 55)),
    ("Betty", datetime(2023, 10, 1, 10, 0), datetime(2023, 10, 1, 10, 26)),
    ("Brian", datetime(2023, 10, 1, 10, 45), datetime(2023, 10, 1, 11, 34)),
    ("Ashley", datetime(2023, 10, 1, 11, 30), datetime(2023, 10, 1, 11, 46)),
    ("Joseph", datetime(2023, 10, 1, 12, 30), datetime(2023, 10, 1, 12, 41)),
    ("Stephanie", datetime(2023, 10, 1, 14, 15), datetime(2023, 10, 1, 14, 30)),
    ("Lisa", datetime(2023, 10, 1, 16, 30), datetime(2023, 10, 1, 16, 45)),
    ("Patricia", datetime(2023, 10, 1, 17, 30), datetime(2023, 10, 1, 19, 30)),
    ("Karen", datetime(2023, 10, 1, 19, 30), datetime(2023, 10, 1, 21, 15)),
]

# Print the final schedule
print("SOLUTION:")
for friend_name, start_time, end_time in schedule:
    print(f"{friend_name}: {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}")