total_distance = (
    (Embarcadero_to_Financial_District * (stephanie_meeting - start_time >= 0)) +
    (Embarcadero_to_Alamo_Square * (john_meeting - start_time >= 0)) +
    (Financial_District_to_Embarcadero * ((stephanie_meeting - start_time >= 0) & (stephanie_meeting - start_time <= 3 * 60))) +
    (Financial_District_to_Alamo_Square * ((stephanie_meeting - start_time >= 0) & (stephanie_meeting - start_time <= john_meeting))) +
    (Alamo_Square_to_Embarcadero * ((john_meeting - start_time >= 0) & (john_meeting - start_time <= 11 * 60))) +
    (Alamo_Square_to_Financial_District * ((john_meeting - start_time >= 0) & (john_meeting - start_time <= 11 * 60)))
)