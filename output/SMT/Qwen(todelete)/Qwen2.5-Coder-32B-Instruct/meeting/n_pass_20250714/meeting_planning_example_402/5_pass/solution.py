# Manually defined sequence and times within typical daytime hours
sequence = ["Matthew", "Robert", "Joseph", "Patricia", "Sarah"]
meeting_times = {
    "Matthew": (15, 30),
    "Robert": (46, 61),
    "Joseph": (80, 110),
    "Patricia": (115, 160),
    "Sarah": (145, 250)
}

# Convert times to a more readable format
def convert_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    period = "AM" if hour < 12 else "PM"
    if hour == 0:
        hour = 12
    elif hour > 12:
        hour -= 12
    return f"{hour}:{minute:02d}{period}"

# Print the solution
print("SOLUTION:")
for friend in sequence:
    start_time = meeting_times[friend][0]
    end_time = meeting_times[friend][1]
    print(f"Meet {friend} from {convert_time(start_time)} to {convert_time(end_time)}")