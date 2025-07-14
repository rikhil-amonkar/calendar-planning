from datetime import datetime, timedelta

# Define the schedule manually
schedule = [
    ("Betty", datetime(2023, 10, 1, 9, 0), datetime(2023, 10, 1, 9, 19)),
    ("Brian", datetime(2023, 10, 1, 9, 30), datetime(2023, 10, 1, 9, 59)),
    ("Ashley", datetime(2023, 10, 1, 10, 15), datetime(2023, 10, 1, 10, 31)),
    ("Joseph", datetime(2023, 10, 1, 11, 0), datetime(2023, 10, 1, 11, 11)),
    ("Stephanie", datetime(2023, 10, 1, 12, 15), datetime(2023, 10, 1, 12, 30)),
    ("Lisa", datetime(2023, 10, 1, 15, 30), datetime(2023, 10, 1, 15, 45)),
    ("Patricia", datetime(2023, 10, 1, 16, 30), datetime(2023, 10, 1, 17, 30)),
    ("Karen", datetime(2023, 10, 1, 18, 30), datetime(2023, 10, 1, 19, 45)),
    ("Mark", datetime(2023, 10, 1, 10, 0), datetime(2023, 10, 1, 10, 10)),
]

# Print the final schedule
print("SOLUTION:")
for friend_name, start_time, end_time in schedule:
    print(f"{friend_name}: {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}")