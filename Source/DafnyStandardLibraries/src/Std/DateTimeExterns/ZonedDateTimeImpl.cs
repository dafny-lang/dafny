namespace ZonedDateTimeImpl {
    
    using System;
    using System.Globalization;
    using System.Linq;
    using System.Numerics;
    using Dafny;

    static class Pack {
        public static ISequence<int> Ints(params int[] xs) =>
            Sequence<int>.FromArray(xs);
        public static ISequence<Rune> Str(string s) =>
            Sequence<Rune>.FromArray(s.EnumerateRunes().Select(r => new Rune(r.Value)).ToArray());
    }

    public static class __default {
        static TimeZoneInfo GetTz(string zoneId) {
            // If zoneId is null or empty, use the local time zone
            if (string.IsNullOrEmpty(zoneId)) {
                return TimeZoneInfo.Local;
            }
            return TimeZoneInfo.FindSystemTimeZoneById(zoneId);
        }

        public static ISequence<int> ResolveLocal(
            ISequence<Rune> zoneIdSeq,
            int year, int month, int day,
            int hour, int minute, int second, int millisecond,
            Std.ZonedDateTime._IOverlapResolutionPreference overlapPreference,
            Std.ZonedDateTime._IGapResolutionPreference gapPreference) {

            string zoneId = new string(zoneIdSeq.Elements.Select(r => (char)r.Value).ToArray());
            var tz = GetTz(zoneId);

            var local = new DateTime(year, month, day,
                                     hour, minute, second, millisecond,
                                     (int)DateTimeKind.Unspecified);

            // Check if the time is INVALID (does not exist, e.g., during spring DST transition)
            if (tz.IsInvalidTime(local)) {
                // If preference is ERROR, return error
                if (gapPreference.is_Error /* ERROR */) {
                    var errorComponents = new int[]
                    {
                        3 /* ERROR */,
                        0,
                        0, 0, 0,
                        0, 0, 0, 0
                    };
                    return Pack.Ints(errorComponents);
                }
                if (gapPreference.is_ShiftForward /* SHIFT_FORWARD */) {
                    // Shift forward to the next valid time
                    DateTime probe = local;
                    while (tz.IsInvalidTime(probe)) {
                        probe = probe.AddMinutes(1);
                    }

                    var offset = tz.GetUtcOffset(probe);
                    var components = new int[]
                    {
                        2 /* GAP */,
                        (int)offset.TotalMinutes,
                        probe.Year, probe.Month, probe.Day,
                        probe.Hour, probe.Minute, probe.Second, probe.Millisecond
                    };
                    return Pack.Ints(components);
                }
                // Exception: unknown gap preference
                throw new Exception("Unknown gap resolution preference");
            }

            // It's a valid time
            // Check if the time is OVERLAP 
            // (there are two possible times if clocks were set back during DST transition)
            if (tz.IsAmbiguousTime(local)) {
                // If preference is ERROR, return error
                if (overlapPreference.is_Error /* ERROR */) {
                    var errorComponents = new int[]
                    {
                        3 /* ERROR */,
                        0,
                        0, 0, 0,
                        0, 0, 0, 0
                    };
                    return Pack.Ints(errorComponents);
                }

                var offsets = tz.GetAmbiguousTimeOffsets(local);

                DateTimeOffset Make(DateTime dt, TimeSpan off) =>
                    new DateTimeOffset(dt, off); // auto compares using UTC instants

                var chosen = overlapPreference.is_PreferEarlier
                    ? offsets.MinBy(off => Make(local, off))   // Prefer earlier UTC instant
                    : offsets.MaxBy(off => Make(local, off));  // Prefer later UTC instant

                // Return the chosen offset and the local time   
                var dto = new DateTimeOffset(local, chosen);
                var norm = dto.LocalDateTime;
                var components = new int[]
                {
                    1 /* OVERLAP */,
                    (int)chosen.TotalMinutes,
                    norm.Year, norm.Month, norm.Day,
                    norm.Hour, norm.Minute, norm.Second, norm.Millisecond
                };
                return Pack.Ints(components);
            }

            // Normal case (UNIQUE): just return the offset and the local time
            var offsetNormal = tz.GetUtcOffset(local);
            var componentsNormal = new int[]
            {
            0 /* NORMAL */,
            (int)offsetNormal.TotalMinutes,
            local.Year, local.Month, local.Day,
            local.Hour, local.Minute, local.Second, local.Millisecond
            };
            return Pack.Ints(componentsNormal);
        }

        public static ISequence<int> NowZoned() {
            var now = DateTimeOffset.Now; // includes offset
            var components = new int[] {
            (int)now.Offset.TotalMinutes,
            now.Year,
            now.Month,
            now.Day,
            now.Hour,
            now.Minute,
            now.Second,
            now.Millisecond
        };
            return Sequence<int>.FromArray(components);
        }

        public static ISequence<Rune> GetNowZoneId() {
            var zid = TimeZoneInfo.Local.Id;
            return Pack.Str(zid);
        }

    }
}