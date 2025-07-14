# Manually defined sequence and times within typical daytime hours
sequence = ["Matthew", "Robert", "Joseph", "Patricia", "Sarah"]
meeting_times = {
    "Matthew": (15, 30),
    "Robert": (46, 61),
    "Joseph": (80, 110),
    "Patricia": (115, 160),
    "Sarah": (150, 255)
}

# Convert times to a more readable format
def convert_time(minutes):
    return f"{minutes // 60}:{minutes % 60:02d}AM"

# Print the solution
print("SOLUTION:")
for friend in sequence:
    start_time = meeting_times[friend][0]
    end_time = meeting_times[friend][1]
    print(f"Meet {friend} from {convert_time(start_time)} to {convert_time(end_time)}")