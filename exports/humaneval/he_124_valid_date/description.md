# he_124_valid_date

`validDate(date : String) : Bool`

Validate a given date string and return true if the date is valid. The date is valid if: it is not empty; the number of days is not less than 1 or higher than 31 for months 1,3,5,7,8,10,12, not higher than 30 for months 4,6,9,11 and not higher than 29 for month 2; the month is between 1 and 12; and the format is mm-dd-yyyy.
