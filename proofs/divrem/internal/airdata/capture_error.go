package airdata

// A value of this concrete type is a non-nil error without a formatting call.
type captureError string

func (e captureError) Error() string { return string(e) }
